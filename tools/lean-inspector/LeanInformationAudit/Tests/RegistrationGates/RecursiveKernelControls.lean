import LeanInformationAudit.Tests.RegistrationGates.DeclaredRecursion
import LeanInformationAudit.Tests.RegistrationGates.RecursivePrograms

namespace LeanInformationAudit.Tests.RecursiveKernelControls
open Lean Meta Elab Command TemplateAudit
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

def copy : List Bool → List Bool
  | [] => []
  | x :: xs => x :: copy xs

def all : List Bool → Bool
  | [] => true
  | x :: xs => Bool.and x (all xs)

def recursiveReadout (xs : List Bool) : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun b => Bool.and b (all xs))

def rawNat (n : Nat) : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun b => Nat.rec b (fun _ r => r) n)

def unsupported (n : Nat) : Bool :=
  if h : n = 0 then true else unsupported (n - 1)
termination_by n
decreasing_by omega

def wellFoundedReadout (n : Nat) : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun _ => unsupported n)

mutual
def mutualLeft : List Bool → Bool
  | [] => true
  | _ :: xs => mutualRight xs
def mutualRight : List Bool → Bool
  | [] => false
  | _ :: xs => mutualLeft xs
end

def mutualReadout (xs : List Bool) : PrimitiveRealization (cutSignature Bool Bool) :=
  cutRealization (fun _ => mutualLeft xs)

def recursiveTemplate : List Bool → PrimitiveRealization (cutSignature Bool Bool)
  | [] => cutRealization id
  | _ :: xs => recursiveTemplate xs

elab "check_recursive_kernel_controls" : command => do
  for (name, expected) in #[(``recursiveReadout, none),
      (``rawNat, some "unclassified_form:E4.recursion:Nat.rec"),
      (``wellFoundedReadout, some "unclassified_form:E5.recursive_definition"),
      (``mutualReadout, some "unclassified_form:E5.recursive_definition"),
      (``recursiveTemplate, some "unclassified_form:E1.recursive_definition")] do
    let saved ← get
    let result ← enroll name #[`List]
    let selected := selectedPlan (← getEnv) name
    set saved
    let actual := match result with | .ok () => none | .error reason => some reason
    unless actual == expected do
      logError m!"[FAIL] kernel_control {name}: {repr actual}"
    if actual == expected then logInfo m!"[PASS] kernel_control {name}: {repr actual}"
    if let .ok plan := selected then
      logInfo m!"PLAN_METRICS {name} bytes={plan.serializedBytes} work={plan.chargedWork} dependencies={plan.dependencies.size}"
      unless plan.rules.contains "E5.finite_kernel_definition" do
        logError "[FAIL] recursive rule was not exercised"

check_recursive_kernel_controls

end LeanInformationAudit.Tests.RecursiveKernelControls
