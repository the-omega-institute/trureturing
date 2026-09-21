import LeanInformationAudit.Tests.RegistrationGates.DeclaredProofBindings

namespace LeanInformationAudit.Tests.DeclaredOpaqueProofShapes
open Lean Meta Elab Command TemplateAudit TemplateBinding
open D5.S3.ConceptDynamics.InformationEscape RegistrationTemplates

def constructorProbe (f : Bool → Bool) :
    PrimitiveRealization (cutSignature Bool Bool) := cutRealization f

-- Positivity checks the reduced field proposition. Its raw proof contains a
-- self-reference that the enrollment judge must never visit.
elab "observe_constructor_hidden_proof" : command => do
  let initial ← get
  let ast := (← getCurrNamespace).str "HiddenProofAST"
  let hidden := Expr.letE `hidden (mkSort (.succ .zero)) (mkConst ast)
    (mkConst ``True.intro) false
  let domain := Expr.letE `h (mkConst ``True) hidden (mkConst ``True) false
  let ctorType := mkForall `h .default domain (mkConst ast)
  liftCoreM <| addDecl (.inductDecl [] 0
    [{ name := ast, type := mkSort (.succ .zero),
       ctors := [{ name := ast.str "mk", type := ctorType }] }] false)
  let result ← enroll ``constructorProbe #[ast]
  let retained := (selectedPlan (← getEnv) ``constructorProbe).isOk
  set initial
  let ok := result.isOk && retained
  (if ok then logInfo else logError)
    m!"[{if ok then "PASS" else "FAIL"}] constructor_hidden_proof_opaque result={repr result}"

observe_constructor_hidden_proof

def proofTemplate (_h : True) (f : Bool → Bool) :
    PrimitiveRealization (cutSignature Bool Bool) := cutRealization f
def forwardTerm (h : True) (f : Bool → Bool) := proofTemplate h f
def forwardLet (h : True) (f : Bool → Bool) :=
  proofTemplate (let _saved := h; True.intro) f

register_information_template proofTemplate

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature := cutSignature Bool Bool
  Law r := ∀ x : Bool, r.readout () x = x.not.not
instance : DecidableEq arena.State := instDecidableEqBool

information_theorem termLaw in arena
  readout via (proofTemplate True.intro (fun x => x))
  primitives (forwardTerm True.intro (fun x => x))
  : ∀ x : Bool, x = x.not.not := by intro x; exact (Bool.not_not x).symm

information_theorem letLaw in arena
  readout via (proofTemplate True.intro (fun x => x))
  primitives (forwardLet True.intro (fun x => x))
  : ∀ x : Bool, x = x.not.not := by intro x; exact (Bool.not_not x).symm

elab "observe_forward_proof_shapes" : command => do
  for (label, name) in #[("forward_proof_term_validated", ``termLaw),
      ("forward_proof_let_validated", ``letLaw)] do
    let record := (records (← getEnv)).find? (·.occurrence.key.theoremName == name)
    let ok := record.any fun row => row.result matches .declaredValidated _
    (if ok then logInfo else logError) m!"[{if ok then "PASS" else "FAIL"}] {label}"
    if let some { result := .declaredUnresolved diagnostic, .. } := record then logInfo diagnostic

observe_forward_proof_shapes

end LeanInformationAudit.Tests.DeclaredOpaqueProofShapes
