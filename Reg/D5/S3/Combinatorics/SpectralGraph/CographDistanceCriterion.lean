import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Combinatorics.SpectralGraph.CographDistanceCriterion

/-! The distinct root count in the native finite candidate criterion. -/

namespace Reg.D5.S3.Combinatorics.SpectralGraph.CographDistanceCriterion

open LeanInformationAudit SimpleGraph Polynomial
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Reg.Support.SingleDependentReadout (signature sensitivity)
open _root_.D5.S3.Combinatorics.SpectralGraph.CographDistanceCotree
open _root_.D5.S3.Combinatorics.SpectralGraph.CographVicinalWidth (width)
open _root_.D5.S3.Combinatorics.SpectralGraph.NormalizedCographCotree (Cotree)
open _root_.D5.S3.QuadraticForms.SymmetricRankOneKernel (realGuardCandidates)
open scoped BigOperators

set_option autoImplicit false

noncomputable section

abbrev countSignature := signature Unit (fun _ => Finset ℝ) (fun _ => ℕ)

abbrev countArena : Arena where
  signature := countSignature
  Law R := ∀ {V : Type} [Finite V] {G : SimpleGraph V} {kind : Option Bool}
    (tree : Cotree G kind) (_hc : G.Connected) (_hP : ¬(pathGraph 4).IsIndContained G),
    let s := (cotreeGuardData tree 0).subtreeGuards
    let candidates := realGuardCandidates s id
    R.readout () () candidates ≤ ∑ p ∈ s, p.natDegree ∧
      ∀ x : ℝ, (Eligible x ∧ distanceMultiplicity G x = width G) ↔
        x ∈ candidates ∧ Eligible x ∧ (cotreeScalarState tree x 0).1 = width G

private def actual : Realization countSignature :=
  realize countSignature (fun _ _ candidates => candidates.card) (fun e => nomatch e)

private def rejected : Realization countSignature :=
  realize countSignature (fun _ _ _ => 2) (fun e => nomatch e)

private theorem rejectedLaw : ¬ countArena.Law rejected := by
  intro h
  let G : SimpleGraph Unit := ⊥
  let leaf : Cotree G none := .leaf () (fun _ => Subsingleton.elim _ _)
  have hc : G.Connected := connected_bot_iff.mpr ⟨inferInstance, inferInstance⟩
  have hp : ¬(pathGraph 4).IsIndContained G := by
    rintro ⟨e⟩
    exact (by decide : (0 : Fin 4) ≠ 1) (e.injective (Subsingleton.elim (e 0) (e 1)))
  have bound := (h leaf hc hp).1
  change 2 ≤ ∑ p ∈ ({X + C (0 : ℤ)} : Finset ℤ[X]), p.natDegree at bound
  simp at bound

def countSource : Registration countArena (type_of% @distanceMultiplicity_guard_candidates) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@distanceMultiplicity_guard_candidates, rejected, rejectedLaw⟩
  sensitivity := sensitivity countArena.Law actual rejected rejectedLaw
  dependence := by
    intro _
    refine ⟨(), ∅, {0}, ?_⟩
    change (∅ : Finset ℝ).card ≠ ({0} : Finset ℝ).card
    simp

def countRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@distanceMultiplicity_guard_candidates) (Realization countSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.SpectralGraph.CographDistanceCriterion.countUnit
  realizationName := `Reg.D5.S3.Combinatorics.SpectralGraph.CographDistanceCriterion.countSource
  realizationSource := none
  generated := false
  arena := .source ⟨countArena⟩
  objectArena := .source ⟨countArena⟩
  catalog := .anonymous
  localNames := false
  realization := .source countArena ⟨countSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize countSignature (fun _ _ candidates => candidates.card)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.SpectralGraph.CographDistanceCriterion
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Combinatorics.SpectralGraph.CographDistanceCriterion
