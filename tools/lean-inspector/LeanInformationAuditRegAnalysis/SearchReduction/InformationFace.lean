import LeanInformationAudit.AuricFibCapture

/-! Optional information evidence never enters the computational classifier. -/
namespace LeanInformationAudit.SearchReduction
open Lean

inductive InformationFace where
  | strictBound | collapsedBound | unknownBound
  | notBound (reason : String)
  | notSubmitted
  deriving BEq, Repr, Inhabited

def InformationFace.label : InformationFace → String
  | .strictBound => "strict-bound"
  | .collapsedBound => "collapsed-bound"
  | .unknownBound => "unknown-bound"
  | .notBound reason => s!"not-bound({reason})"
  | .notSubmitted => "not-submitted"

structure InformationReading where
  face : InformationFace := .notSubmitted
  application : Option Name := none
  registration : Option Name := none
  ordinaryRecords : Array Json := #[]

end LeanInformationAudit.SearchReduction
