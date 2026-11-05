import Lean

/-! Shared evidence classifier used by compiled acquisition and its model. -/
namespace LeanInformationAudit.AuricFib

inductive Capture where
  | strict | collapsed | unknown
  deriving DecidableEq, Repr

def classifyCapture (separated identifiable : Bool) : Capture :=
  if separated then .strict else if identifiable then .collapsed else .unknown

def Capture.label : Capture → String
  | .strict => "strict" | .collapsed => "collapsed" | .unknown => "unknown"

def taskCapture (family : Capture) (usesDelta : Bool) : Capture :=
  if usesDelta then family else .collapsed

end LeanInformationAudit.AuricFib
