import LeanInformationAudit.ReadoutProvenance
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import Mathlib.Algebra.Field.ZMod

open Lean LeanInformationAudit.RegistrationGates
open D5.S3.ConceptDynamics.InformationEscape

namespace DeclaredFieldParameters

theorem target : (137 : Nat) = 137 := rfl
theorem existentialTarget : ∃ b : Bool, b = b := ⟨true, rfl⟩

def plain (_ : Unit) (state : Bool) : Bool := state
def arenaCardRead (_ : Unit) (state : Bool) : Bool :=
  let _ := (Arena.ofFintype Bool).card
  state
def catalogIndexCard {arena : Arena.{0}} (catalog : Catalog.{0,0,0} arena) : Nat :=
  letI := catalog.indexFintype
  Fintype.card catalog.Index
def catalogCarrierRead (_ : Unit) (state : Bool) : Bool :=
  let _ := @catalogIndexCard
  state
def bundleIndexCard (bundle : D5.S3.ConceptDynamics.CIRPT.PrimitiveBundle.{0,0} Bool) : Nat :=
  letI := bundle.indexFintype
  Fintype.card bundle.Index
def bundleCarrierRead (_ : Unit) (state : Bool) : Bool :=
  let _ := bundleIndexCard
  state
def functionInterfaceRead (_ : Unit) (state : Bool) : Bool :=
  let _ : DFunLike (ZMod 2 →+* ZMod 2) (ZMod 2) (fun _ => ZMod 2) := inferInstance
  state
def fieldRead (_ : Unit) (state : Bool) : Bool :=
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Field (ZMod 2) := inferInstance
  state

def hiddenArena : Arena where
  State := PLift ((137 : Nat) = 137)
  stateFintype := ⟨{⟨rfl⟩}, by intro ⟨h⟩; simp⟩
  stateDecidableEq := fun a b => .isTrue (Subsingleton.elim a b)
def hiddenArenaRead (_ : Unit) (state : Bool) : Bool :=
  let _ := hiddenArena.card
  state
def hiddenFunctionInterface : DFunLike (PLift ((137 : Nat) = 137)) Unit (fun _ => Bool) where
  coe _ _ := true
  coe_injective := by intro a b _; cases a; cases b; rfl
def hiddenFunctionInterfaceRead (_ : Unit) (state : Bool) : Bool :=
  let _ := hiddenFunctionInterface
  state
def hiddenList (_ : Unit) (state : Bool) : Bool :=
  let _ : List (PLift ((137 : Nat) = 137)) := [⟨rfl⟩]
  state

-- Observe the production walker without turning a semantic failure into a
-- compiler error. Each query starts from the same native environment.
run_cmd Elab.Command.liftCoreM do
  for (label, readout, theoremName, clean) in #[
      ("arena_parameter_role_accepted", ``arenaCardRead, ``target, true),
      ("catalog_parameter_role_accepted", ``catalogCarrierRead, ``target, true),
      ("bundle_parameter_role_accepted", ``bundleCarrierRead, ``target, true),
      ("function_parameter_role_accepted", ``functionInterfaceRead, ``existentialTarget, true),
      ("field_parameter_role_accepted", ``fieldRead, ``existentialTarget, true),
      ("independent_field_parameter_control_accepted", ``plain, ``target, true),
      ("parameter_arena_statement_incomplete", ``hiddenArenaRead, ``target, false),
      ("parameter_function_statement_rejected", ``hiddenFunctionInterfaceRead, ``target, false),
      ("parameter_list_statement_rejected", ``hiddenList, ``target, false)] do
    let saved ← getEnv
    let some (.defnInfo _) := saved.find? readout | throwError "setup: missing readout {readout}"
    let (rejected, closure) ← readoutClosureCurrent theoremName (mkConst readout)
    setEnv saved
    let ok := if label == "parameter_arena_statement_incomplete" then
        !rejected && closure.isNone
      else if clean then !rejected && closure.isSome else rejected && closure.isSome
    logInfo m!"[{if ok then "PASS" else "FAIL"}] {label} rejected={rejected} complete={closure.isSome}"

end DeclaredFieldParameters
