import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Topology.TauCeti.AlgebraicTopology.FundamentalGroupoid.NeighborhoodCover


/-
  Faithful typed four-slot audit attempt for the complete neighborhood-cover
  extension theorem. The source target and DependentFamily obligations are
  compiled here; source occurrence evidence remains subject to the current
  report and is not asserted as validated by this file.
-/
namespace Reg.D5.S3.Topology.TauCeti.AlgebraicTopology.FundamentalGroupoid.NeighborhoodCover
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.TauCeti.FundamentalGroupoid

abbrev sourceStatement.{a,b,c,d} : Prop :=
  type_of% (@_root_.TauCeti.FundamentalGroupoid.existsUnique_extension.{a,b,c,d})

abbrev signature : Signature where
  Params := Unit
  State _ := Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ b => b) (fun e _ => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e _ => nomatch e)

def arena.{a,b,c,d} : Arena where
  signature := signature
  Law R := sourceStatement.{a,b,c,d} ∧
    ∀ p, R.readout () () p = p

theorem actual_bridge.{a,b,c,d} :
    sourceStatement.{a,b,c,d} ↔ arena.{a,b,c,d}.Law actual := by
  simp [arena, actual, realize]

theorem rejected_law.{a,b,c,d} : ¬ arena.{a,b,c,d}.Law rejected := by
  intro h
  have hp := h.2 true
  simpa [arena, rejected, realize] using hp

def source.{a,b,c,d} : Registration (arena.{a,b,c,d}) (sourceStatement.{a,b,c,d}) where
  actual := actual
  bridge := actual_bridge
  variation := ⟨actual_bridge.{a,b,c,d}.mp (by exact @_root_.TauCeti.FundamentalGroupoid.existsUnique_extension.{a,b,c,d}), rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law.{a,b,c,d}⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    cases i
    exact ⟨(), false, true, by change false ≠ true; decide⟩

noncomputable def registration.{a,b,c,d} : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.TauCeti.FundamentalGroupoid.existsUnique_extension.{a,b,c,d})
    (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Topology.TauCeti.AlgebraicTopology.FundamentalGroupoid.NeighborhoodCover.extension,
  realizationName := `Reg.D5.S3.Topology.TauCeti.AlgebraicTopology.FundamentalGroupoid.NeighborhoodCover.source,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena⟩,
  objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (arena.{a,b,c,d}) ⟨source.{a,b,c,d}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ _ b => b) (fun e _ => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Topology.TauCeti.AlgebraicTopology.FundamentalGroupoid.NeighborhoodCover,
    definition := none,
    coordinates := #[],
    readouts := #[{
      path := #["arg", "body", "body", "body", "body", "body"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := some #["fn", "arg"],
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[] }

#print axioms registration
end Reg.D5.S3.Topology.TauCeti.AlgebraicTopology.FundamentalGroupoid.NeighborhoodCover
