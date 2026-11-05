import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam
import Reg.Support.DependentFamily

/-! Original finite-count laws with source-indexed numerical observations. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam

namespace Reg.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam

noncomputable section

abbrev countSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def lowerActual : Realization countSignature :=
  realize countSignature (fun _ _ n => freeCount (n - 1)) (fun e => nomatch e)

def lowerRejected : Realization countSignature :=
  realize countSignature (fun _ _ n => (torusCount n) + 1) (fun e => nomatch e)

def lowerArena : Arena where
  signature := countSignature
  Law r := ∀ n : ℕ, r.readout () () n ≤ torusCount n

private theorem lowerRejectedLaw : ¬ lowerArena.Law lowerRejected := by
  intro h
  have hf := h 0
  change (torusCount (0 : ℕ)) + 1 ≤ torusCount (0 : ℕ) at hf
  omega

private theorem lowerDependence : ObservationalDependence countSignature lowerActual := by
  intro i
  refine ⟨(), 0, 2, ?_⟩
  norm_num [lowerActual, realize, a063443, tilingPlacements, peak, coefficient,
    torusCount, freeCount, independentSets, board, torusAdjacent, freeAdjacent, gap,
    Finset.range_succ, Finset.powerset_insert]

def lowerFamily : Registration lowerArena
    (type_of% (@_root_.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam.free_le_torus)) where
  actual := lowerActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam.free_le_torus,
    lowerRejected, lowerRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨lowerRejected, ?_, rfl, lowerRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e
      exact nomatch e
  dependence := lowerDependence

noncomputable def lowerRegistration : Contract.Registration
    (@_root_.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam.free_le_torus)
    (Realization countSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam.free_le_torus.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam.lowerFamily
  realizationSource := none
  generated := false
  arena := .source ⟨lowerArena⟩
  objectArena := .source ⟨lowerArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source lowerArena ⟨lowerFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some lowerActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def upperActual : Realization countSignature :=
  realize countSignature (fun _ _ n => torusCount n) (fun e => nomatch e)

def upperRejected : Realization countSignature :=
  realize countSignature (fun _ _ n => (freeCount n) + 1) (fun e => nomatch e)

def upperArena : Arena where
  signature := countSignature
  Law r := ∀ n : ℕ, r.readout () () n ≤ freeCount n

private theorem upperRejectedLaw : ¬ upperArena.Law upperRejected := by
  intro h
  have hf := h 0
  change (freeCount (0 : ℕ)) + 1 ≤ freeCount (0 : ℕ) at hf
  omega

private theorem upperDependence : ObservationalDependence countSignature upperActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [upperActual, realize, a063443, tilingPlacements, peak, coefficient,
    torusCount, freeCount, independentSets, board, torusAdjacent, freeAdjacent, gap,
    Finset.range_succ, Finset.powerset_insert]

def upperFamily : Registration upperArena
    (type_of% (@_root_.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam.torus_le_free)) where
  actual := upperActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam.torus_le_free,
    upperRejected, upperRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨upperRejected, ?_, rfl, upperRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e
      exact nomatch e
  dependence := upperDependence

noncomputable def upperRegistration : Contract.Registration
    (@_root_.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam.torus_le_free)
    (Realization countSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam.torus_le_free.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam.upperFamily
  realizationSource := none
  generated := false
  arena := .source ⟨upperArena⟩
  objectArena := .source ⟨upperArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source upperArena ⟨upperFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some upperActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def modalLossActual : Realization countSignature :=
  realize countSignature (fun _ _ n => torusCount n) (fun e => nomatch e)

def modalLossRejected : Realization countSignature :=
  realize countSignature (fun _ _ n => ((n ^ 2 + 1) * peak n) + 1) (fun e => nomatch e)

def modalLossArena : Arena where
  signature := countSignature
  Law r := ∀ n : ℕ, r.readout () () n ≤ (n ^ 2 + 1) * peak n

private theorem modalLossRejectedLaw : ¬ modalLossArena.Law modalLossRejected := by
  intro h
  have hf := h 0
  change (((0 : ℕ) ^ 2 + 1) * peak (0 : ℕ)) + 1 ≤ ((0 : ℕ) ^ 2 + 1) * peak (0 : ℕ) at hf
  omega

private theorem modalLossDependence : ObservationalDependence countSignature modalLossActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [modalLossActual, realize, a063443, tilingPlacements, peak, coefficient,
    torusCount, freeCount, independentSets, board, torusAdjacent, freeAdjacent, gap,
    Finset.range_succ, Finset.powerset_insert]

def modalLossFamily : Registration modalLossArena
    (type_of% (@_root_.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam.count_le_mul_peak)) where
  actual := modalLossActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam.count_le_mul_peak,
    modalLossRejected, modalLossRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨modalLossRejected, ?_, rfl, modalLossRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e
      exact nomatch e
  dependence := modalLossDependence

noncomputable def modalLossRegistration : Contract.Registration
    (@_root_.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam.count_le_mul_peak)
    (Realization countSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam.count_le_mul_peak.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam.modalLossFamily
  realizationSource := none
  generated := false
  arena := .source ⟨modalLossArena⟩
  objectArena := .source ⟨modalLossArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source modalLossArena ⟨modalLossFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some modalLossActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def modalUpperActual : Realization countSignature :=
  realize countSignature (fun _ _ n => peak n) (fun e => nomatch e)

def modalUpperRejected : Realization countSignature :=
  realize countSignature (fun _ _ n => (torusCount n) + 1) (fun e => nomatch e)

def modalUpperArena : Arena where
  signature := countSignature
  Law r := ∀ n : ℕ, r.readout () () n ≤ torusCount n

private theorem modalUpperRejectedLaw : ¬ modalUpperArena.Law modalUpperRejected := by
  intro h
  have hf := h 0
  change (torusCount (0 : ℕ)) + 1 ≤ torusCount (0 : ℕ) at hf
  omega

private theorem modalUpperDependence : ObservationalDependence countSignature modalUpperActual := by
  intro i
  refine ⟨(), 0, 2, ?_⟩
  norm_num [modalUpperActual, realize, a063443, tilingPlacements, peak, coefficient,
    torusCount, freeCount, independentSets, board, torusAdjacent, freeAdjacent, gap,
    Finset.range_succ, Finset.powerset_insert]

def modalUpperFamily : Registration modalUpperArena
    (type_of% (@_root_.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam.peak_le_count)) where
  actual := modalUpperActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam.peak_le_count,
    modalUpperRejected, modalUpperRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨modalUpperRejected, ?_, rfl, modalUpperRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e
      exact nomatch e
  dependence := modalUpperDependence

noncomputable def modalUpperRegistration : Contract.Registration
    (@_root_.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam.peak_le_count)
    (Realization countSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam.peak_le_count.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam.modalUpperFamily
  realizationSource := none
  generated := false
  arena := .source ⟨modalUpperArena⟩
  objectArena := .source ⟨modalUpperArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source modalUpperArena ⟨modalUpperFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some modalUpperActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def tilingActual : Realization countSignature :=
  realize countSignature (fun _ _ n => a063443 n) (fun e => nomatch e)

def tilingRejected : Realization countSignature :=
  realize countSignature (fun _ _ n => (freeCount (n - 1)) + 1) (fun e => nomatch e)

def tilingArena : Arena where
  signature := countSignature
  Law r := ∀ n : ℕ, r.readout () () n = freeCount (n - 1)

private theorem tilingRejectedLaw : ¬ tilingArena.Law tilingRejected := by
  intro h
  have hf := h 0
  change (freeCount ((0 : ℕ) - 1)) + 1 = freeCount ((0 : ℕ) - 1) at hf
  omega

private theorem tilingDependence : ObservationalDependence countSignature tilingActual := by
  intro i
  refine ⟨(), 0, 2, ?_⟩
  norm_num [tilingActual, realize, a063443, tilingPlacements, peak, coefficient,
    torusCount, freeCount, independentSets, board, torusAdjacent, freeAdjacent, gap,
    Finset.range_succ, Finset.powerset_insert]

def tilingFamily : Registration tilingArena
    (type_of% (@_root_.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam.tiling_free_identity)) where
  actual := tilingActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam.tiling_free_identity,
    tilingRejected, tilingRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨tilingRejected, ?_, rfl, tilingRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e
      exact nomatch e
  dependence := tilingDependence

noncomputable def tilingRegistration : Contract.Registration
    (@_root_.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam.tiling_free_identity)
    (Realization countSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam.tiling_free_identity.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam.tilingFamily
  realizationSource := none
  generated := false
  arena := .source ⟨tilingArena⟩
  objectArena := .source ⟨tilingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source tilingArena ⟨tilingFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some tilingActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.ToroidalKingsEmptySeam
