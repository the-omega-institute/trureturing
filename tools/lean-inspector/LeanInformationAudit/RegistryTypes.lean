import LeanInformationAudit.TemplateData
import LeanInformationAudit.RuntimeInputs
import LeanInformationAudit.CatalogRecords

namespace LeanInformationAudit
open Lean

/-- Judge-owned semantic API for the lightweight standalone report driver.
The inspector resolves one exact declaration/owner of this type. Content does
not register producers, callbacks, policies or acceptance bits. Each requested
target passes its binding row, generated declaration names and environment
to the consumer before the next target starts. No target environment is retained. The
type uses core types only because the inspector does not import the judge. -/
abbrev InformationTemplateReportDriver := Array Name →
  (Name → Json → Array Name → Environment → MetaM Unit) → MetaM Unit

/-- Original registration root, immutable environment input and caller-selected
options. Both command and report consumers pass the same explicit inputs. -/
structure RegistrationAssessmentInput where
  rootId : Name
  environment : Environment
  options : Options

def RegistrationAssessmentInput.capture {m : Type → Type} [Monad m] [MonadEnv m]
    [MonadOptions m] (rootId : Name) : m RegistrationAssessmentInput := do
  return { rootId, environment := ← getEnv, options := ← getOptions }

private def environmentConstantNames (constants : ConstMap) : Array Name :=
  (SMap.toList constants).toArray.map (·.1) |>.qsort Name.quickLt

/-- Command lifts can rebuild the wrapper while preserving kernel inputs.
Adding a declaration invalidates a captured assessment input. -/
def sameRegistrationEnvironment (a b : Environment) : Bool :=
  a.header.mainModule == b.header.mainModule &&
    a.allImportedModuleNames == b.allImportedModuleNames &&
    -- Command lifts can share the immutable constant map across wrappers.
    -- The proof required by withPtrEq keeps the original comparison as its
    -- logical definition and as the runtime fallback for different maps.
    withPtrEq (Environment.constants a) (Environment.constants b)
      (fun _ => environmentConstantNames (Environment.constants a) ==
        environmentConstantNames (Environment.constants b))
      (by intro h; simp only [h, beq_self_eq_true])

end LeanInformationAudit



namespace LeanInformationAudit.TemplateBinding
open Lean

private structure AssessmentRecords where
  events : Array (Name × TemplateOccurrenceEvent) := #[]
  claims : Array (Name × TemplateBindingClaim) := #[]
  records : Array (Name × BindingRecord) := #[]
  deriving Inhabited

private initialize assessmentRecords : EnvExtension AssessmentRecords ←
  registerEnvExtension (pure {})

def resetAssessmentRecords (env : Environment) : Environment := assessmentRecords.setState env {}

def addOccurrence (env : Environment) (event : TemplateOccurrenceEvent) :
    Environment :=
  assessmentRecords.modifyState env fun state => { state with
    events := state.events.push (event.key.registrationModule, event) }

def addClaim (env : Environment) (claim : TemplateBindingClaim) : Environment :=
  assessmentRecords.modifyState env fun state => { state with
    claims := state.claims.push (claim.owner, claim) }

def addRecord (env : Environment) (record : BindingRecord) : Environment :=
  assessmentRecords.modifyState env fun state => { state with
    records := state.records.push (record.occurrence.key.registrationModule, record) }

def ownedEvents (env : Environment) : Array (Name × TemplateOccurrenceEvent) :=
  (assessmentRecords.getState env).events
def ownedClaims (env : Environment) : Array (Name × TemplateBindingClaim) :=
  (assessmentRecords.getState env).claims
def ownedRecords (env : Environment) : Array (Name × BindingRecord) :=
  (assessmentRecords.getState env).records
def inventory (env : Environment) : Array TemplateOccurrenceEvent := (ownedEvents env).map Prod.snd
def claims (env : Environment) : Array TemplateBindingClaim := (ownedClaims env).map Prod.snd
def records (env : Environment) : Array BindingRecord := (ownedRecords env).map Prod.snd

end LeanInformationAudit.TemplateBinding

namespace LeanInformationAudit.GeneratedDeclarations
open Lean
private structure State where
  owner : Option Name := none
  names : Array (Name × Name) := #[]
  deriving Inhabited
private initialize state : EnvExtension State ← registerEnvExtension (pure {})

def entries (env : Environment) : Array (Name × Name) := (state.getState env).names

def currentOwner (env : Environment) : Name :=
  (state.getState env).owner.getD env.header.mainModule

def ownerOf (env : Environment) (name : Name) : Name :=
  ((entries env).find? (·.1 == name)).map Prod.snd |>.getD
    ((env.getModuleIdxFor? name).map (env.header.moduleNames[·.toNat]!) |>.getD env.header.mainModule)

def record (env : Environment) (name : Name) : Environment :=
  let current := state.getState env
  let owner := current.owner.getD env.header.mainModule
  if (entries env).any (·.1 == name) then env else
    state.setState env { current with names := current.names.push (name, owner) }

def withOwner {m : Type → Type} [Monad m] [MonadEnv m] [MonadFinally m]
    (owner : Name) (action : m α) : m α := do
  let previous := (state.getState (← getEnv)).owner
  modifyEnv fun env => state.modifyState env fun current => { current with owner := some owner }
  try action finally
    modifyEnv fun env => state.modifyState env fun current => { current with owner := previous }
end LeanInformationAudit.GeneratedDeclarations
