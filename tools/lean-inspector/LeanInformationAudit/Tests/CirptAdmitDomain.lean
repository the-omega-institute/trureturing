import D5.S3.ConceptDynamics.CIRPT.SemanticIntegrity
import LeanInformationAudit.SealCommand

/-! T-CIRPT-003: a mixed Bool CUT fiber has an exact nonempty ADMIT defect.
`rg -n "IE-C017" tools/lean-inspector/LeanInformationAudit -g '*.lean'`
finds only this fixture, so the judge has no IE-C017 diagnostic path. The
B2 assertions below pin the required full-domain replacement semantics. -/

open D5.S3.ConceptDynamics.CIRPT
open D5.S3.ConceptDynamics.InformationEscape

namespace LeanInformationAudit.Tests.CirptAdmitDomain

def arena : PrimitiveLawArena where
  toArena := Arena.ofFintype Bool
  signature :=
    { Index := Fin 1
      indexFintype := inferInstance
      indexDecidableEq := inferInstance
      Output := fun _ => Bool
      outputDecidableEq := fun _ => inferInstance
      axis := fun _ => .cut
      readoutAxisNotAnchor := by simp
      AnchorIndex := Fin 0
      anchorFintype := inferInstance
      anchorDecidableEq := inferInstance }
  Law := fun _ => True

local instance : DecidableEq arena.State := arena.toArena.stateDecidableEq
local instance : Fintype arena.State := arena.toArena.stateFintype

def registeredRealization : PrimitiveRealization arena.signature where
  readout := fun _ _ => false
  anchor := Fin.elim0

information_theorem registeredTheorem
  in arena
  primitives registeredRealization
  : arena.Law registeredRealization := by trivial

def admit (state : Bool) : Prop := state = true

local instance admitDecidable (state : Bool) : Decidable (admit state) := by
  unfold admit
  infer_instance

local instance admitDecidablePred : DecidablePred admit :=
  fun state => admitDecidable state

def cut : Bool -> Bool := fun _ => false

example : cut false = cut true := by decide
example : ¬admit false := by simp [admit]
example : admit true := by simp [admit]

example : (false, true) ∈ admitDefect cut admit := by
  change cut false = cut true ∧ ¬(admit false ↔ admit true)
  simp [cut, admit]

example : Set.Nonempty (admitDefect cut admit) :=
  ⟨(false, true), by
    change cut false = cut true ∧ ¬(admit false ↔ admit true)
    simp [cut, admit]⟩

def finiteAdmitDefect : Finset (Bool × Bool) :=
  Finset.univ.filter fun pair => decide (
    (cutKernel cut).relation pair.1 pair.2 ∧
      ¬(admitKernel admit).relation pair.1 pair.2)

example : finiteAdmitDefect.card = 2 := by
  decide

example : ∀ pair, pair ∈ finiteAdmitDefect ↔ pair ∈ admitDefect cut admit := by
  intro pair
  simp [finiteAdmitDefect, admitDefect, kernelResidual]

example : ∀ x y : Bool,
    (flowKernel (id : Bool -> Bool)).relation x y ↔
      (cutKernel (id : Bool -> Bool)).relation x y := by
  decide

def arenaAdmit (state : arena.State) : Prop := state = true

local instance : DecidablePred arenaAdmit := by
  intro state
  unfold arenaAdmit
  exact arena.toArena.stateDecidableEq state true

example :
    admitKernel arenaAdmit =
      cutKernel (fun state => decide (arenaAdmit state)) := by
  exact full_domain_admit_encoding arenaAdmit

example :
    forall pair, pair ∈ offDiagonalPairs arena.State ->
      (bundleWithAtom registeredTheorem.__information_unit.primitives
        { axis := .admit, kernel := admitKernel arenaAdmit }).agrees
          pair.1 pair.2 ->
      registeredTheorem.__information_unit.primitives.agrees pair.1 pair.2 := by
  exact admit_atom_preserves_offDiagonalPairs
    registeredTheorem.__information_unit.primitives arenaAdmit

example (x y : arena.State) :
    (bundleWithAtom registeredTheorem.__information_unit.primitives
      { axis := .admit, kernel := admitKernel arenaAdmit }).agrees x y ->
    registeredTheorem.__information_unit.primitives.agrees x y := by
  exact adding_admit_atom_cannot_increase_agreement
    registeredTheorem.__information_unit.primitives arenaAdmit x y

end LeanInformationAudit.Tests.CirptAdmitDomain
