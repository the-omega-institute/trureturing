import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.SpectralGraph.Cographs.CographDistanceMultiplicity

/-! The order observation for the explicit family in the two-clause result. -/

namespace Reg.D5.S3.Combinatorics.SpectralGraph.Cographs.CographDistanceMultiplicity

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.SingleDependentReadout (signature sensitivity)
open _root_.D5.S3.Combinatorics.SpectralGraph.CographDistanceMultiplicity (result)
open _root_.D5.S3.Combinatorics.SpectralGraph.CographDistanceCotree
  (Eligible distanceMultiplicity distanceMultiplicity_attains_iff)
open _root_.D5.S3.Combinatorics.SpectralGraph.CographVicinalWidth (width)
open _root_.D5.S3.Combinatorics.SpectralGraph.UniversalCliqueCographDistance (Vertex graph family)
open SimpleGraph

set_option autoImplicit false

noncomputable section

private abbrev OrderVertex (s : ℕ) := Vertex (3 * (s - 1)) s s

abbrev orderSignature := signature Unit (fun _ => ℕ) (fun _ => ℕ)

abbrev orderArena : Arena where
  signature := orderSignature
  Law R := (type_of% @distanceMultiplicity_attains_iff) ∧
    ∀ s : ℕ, 2 ≤ s →
      R.readout () () s = 6 * s - 3 ∧
      let G := graph (3 * (s - 1)) s s
      G.Connected ∧ ¬(pathGraph 4).IsIndContained G ∧ width G = 2 ∧
        Eligible ((s : ℝ) - 2) ∧ distanceMultiplicity G ((s : ℝ) - 2) = width G

private def actual : Realization orderSignature :=
  realize orderSignature (fun _ _ s => Fintype.card (OrderVertex s)) (fun e => nomatch e)

private def rejected : Realization orderSignature :=
  realize orderSignature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejectedLaw : ¬ orderArena.Law rejected := by
  intro h
  exact (by decide : (0 : ℕ) ≠ 6 * 2 - 3) (h.2 2 (by decide)).1

def orderSource : Registration orderArena (type_of% @result) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejectedLaw⟩
  sensitivity := sensitivity orderArena.Law actual rejected rejectedLaw
  dependence := by
    intro _
    refine ⟨(), 2, 3, ?_⟩
    change Fintype.card (OrderVertex 2) ≠ Fintype.card (OrderVertex 3)
    rw [(family (show 2 ≤ 2 by decide)).1, (family (show 2 ≤ 3 by decide)).1]
    decide

def orderRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    result (Realization orderSignature) Unit Unit where
  unitName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.Cographs.CographDistanceMultiplicity.orderUnit
  realizationName :=
    `Reg.D5.S3.Combinatorics.SpectralGraph.Cographs.CographDistanceMultiplicity.orderSource
  realizationSource := none
  generated := false
  arena := .source ⟨orderArena⟩
  objectArena := .source ⟨orderArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source orderArena ⟨orderSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize orderSignature
    (fun _ _ s => Fintype.card (OrderVertex s)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.Cographs.CographDistanceMultiplicity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.SpectralGraph.Cographs.CographDistanceMultiplicity
