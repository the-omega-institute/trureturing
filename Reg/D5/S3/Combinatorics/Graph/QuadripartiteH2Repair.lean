import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.QuadripartiteH2Repair
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair
open _root_.D5.S3.Combinatorics.Graph.OctahedralCochainSharpness
open _root_.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair

abbrev geodesicSignature : Signature where
  Params := Cube
  State _ := Cube
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Cochain
  Anchor := Empty
  finiteAnchor := inferInstance

def geodesicActual : Realization geodesicSignature :=
  realize geodesicSignature (fun _ x y => geodesic x y) (fun e => nomatch e)

def geodesicRejected : Realization geodesicSignature :=
  realize geodesicSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev boundaryArena : Arena where
  signature := geodesicSignature
  Law r := ∀ x y b : Cube,
    d2 (r.readout () x y) b =
      (if b = x then 1 else 0) + (if b = y then 1 else 0)

private def x0 : Cube := (false, false, false, false)
private def y1 : Cube := (true, false, false, false)

theorem boundaryRejected_law : ¬ boundaryArena.Law geodesicRejected := by
  intro h
  have hb := h x0 y1 x0
  have hn : ¬ (d2 (0 : Cochain) x0 =
      (if x0 = x0 then 1 else 0) + (if x0 = y1 then 1 else 0)) := by decide
  exact hn hb

theorem geodesicDependence : ObservationalDependence geodesicSignature geodesicActual := by
  intro ⟨⟩
  refine ⟨x0, x0, y1, ?_⟩
  intro h
  have hw := congrArg weight h
  have hn : weight (geodesic x0 x0) ≠ weight (geodesic x0 y1) := by
    rw [geodesic_weight, geodesic_weight]
    decide
  exact hn hw

def boundaryRegistration : Registration boundaryArena
    (∀ x y b : Cube, d2 (geodesic x y) b =
      (if b = x then 1 else 0) + (if b = y then 1 else 0)) where
  actual := geodesicActual
  bridge := Iff.rfl
  variation := ⟨geodesic_boundary, geodesicRejected, boundaryRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨geodesicRejected, ?_, rfl, boundaryRejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro i
      exact nomatch i
  dependence := geodesicDependence

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{2, 2, 0, 1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0} (@_root_.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.geodesic_boundary) (type_of% (boundaryArena)) (type_of% (boundaryArena)) (type_of% (realize.{0, 0, 0, 0, 0} geodesicSignature (fun _ x y => geodesic x y) (fun e => nomatch e))) (Unit) (Unit) (Unit) (Unit) (Unit) := {
  unitName := (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str (Lean.Name.str Lean.Name.anonymous "D5") "S3") "Combinatorics") "Graph") "QuadripartiteH2Repair") "geodesic_boundary") "Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair/Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.boundaryArena/[anonymous]") "__information_unit"),
  realizationName := `Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair.boundaryRegistration,
  realizationSource := none,
  generated := false,
  arena := ⟨(boundaryArena)⟩,
  objectArena := ⟨(boundaryArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source (boundaryArena) ⟨(boundaryRegistration)⟩,
  readout := some (realize.{0, 0, 0, 0, 0} geodesicSignature (fun _ x y => geodesic x y) (fun e => nomatch e)),
  variation := none,
  sensitivity := none,
  escapeFrom := none,
  sourceSelection := some { owner := `D5.S3.Combinatorics.Graph.QuadripartiteH2Repair, definition := none, coordinates := #[0], readouts := #[{ path := #["body", "body", "body", "fn", "arg", "fn", "arg", "fn"], stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }] }


end Reg.D5.S3.Combinatorics.Graph.QuadripartiteH2Repair
