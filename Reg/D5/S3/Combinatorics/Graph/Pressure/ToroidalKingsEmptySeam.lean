import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam
import Reg.Support.DependentFamily

/-! Original finite-count laws with source-indexed numerical observations. -/

open LeanInformationAudit Filter
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam

namespace Reg.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam

noncomputable section

private theorem singleton_powerset (a : ℕ × ℕ) :
    ({a} : Finset (ℕ × ℕ)).powerset = {∅, {a}} := by
  ext s
  simp [Finset.subset_singleton_iff]


private theorem peak_two_gt_one : 1 < peak 2 := by
  classical
  let S : Finset (Finset (ℕ × ℕ)) := {{(0, 0)}, {(0, 1)}}
  have hsub : S ⊆ (independentSets (board 2) (torusAdjacent 2)).filter
      (fun s => s.card = 1) := by
    intro s hs
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl <;>
      norm_num [independentSets, board, torusAdjacent]
  have hcard : S.card = 2 := by decide
  have hc : 2 ≤ coefficient 2 1 := by
    have hh := Finset.card_le_card hsub
    rw [hcard] at hh
    exact hh
  have hm : coefficient 2 1 ≤ peak 2 :=
    Finset.le_sup (by decide : 1 ∈ Finset.range (2 ^ 2 + 1))
  omega

private theorem peak_zero : peak 0 = 1 := by
  norm_num [peak, coefficient, independentSets, board, torusAdjacent,
    Finset.filter_singleton]

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
    Finset.range_add_one, Finset.powerset_insert, Finset.filter_insert, Finset.filter_singleton,
      Finset.product_eq_biUnion, singleton_powerset]

def lowerFamily : Registration lowerArena
    (type_of% (@_root_.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.free_le_torus)) where
  actual := lowerActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.free_le_torus,
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
    (@_root_.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.free_le_torus)
    (Realization countSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.free_le_torus.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.lowerFamily
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
    owner := `D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam
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
    Finset.range_add_one, Finset.powerset_insert, Finset.filter_insert, Finset.filter_singleton,
      Finset.product_eq_biUnion, singleton_powerset]

def upperFamily : Registration upperArena
    (type_of% (@_root_.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.torus_le_free)) where
  actual := upperActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.torus_le_free,
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
    (@_root_.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.torus_le_free)
    (Realization countSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.torus_le_free.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.upperFamily
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
    owner := `D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam
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
  simp only [Nat.zero_pow (by decide : 0 < 2), zero_add, one_mul] at hf
  omega

private theorem modalLossDependence : ObservationalDependence countSignature modalLossActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [modalLossActual, realize, a063443, tilingPlacements, peak, coefficient,
    torusCount, freeCount, independentSets, board, torusAdjacent, freeAdjacent, gap,
    Finset.range_add_one, Finset.powerset_insert, Finset.filter_insert, Finset.filter_singleton,
      Finset.product_eq_biUnion, singleton_powerset]

def modalLossFamily : Registration modalLossArena
    (type_of% (@_root_.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.count_le_mul_peak)) where
  actual := modalLossActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.count_le_mul_peak,
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
    (@_root_.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.count_le_mul_peak)
    (Realization countSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.count_le_mul_peak.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.modalLossFamily
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
    owner := `D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam
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
  change peak 0 ≠ peak 2
  rw [peak_zero]
  exact ne_of_lt peak_two_gt_one

def modalUpperFamily : Registration modalUpperArena
    (type_of% (@_root_.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.peak_le_count)) where
  actual := modalUpperActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.peak_le_count,
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
    (@_root_.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.peak_le_count)
    (Realization countSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.peak_le_count.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.modalUpperFamily
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
    owner := `D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam
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
    Finset.range_add_one, Finset.powerset_insert, Finset.filter_insert, Finset.filter_singleton,
      Finset.product_eq_biUnion, singleton_powerset]

def tilingFamily : Registration tilingArena
    (type_of% (@_root_.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.tiling_free_identity)) where
  actual := tilingActual
  bridge := Iff.rfl
  variation := ⟨@_root_.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.tiling_free_identity,
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
    (@_root_.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.tiling_free_identity)
    (Realization countSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.tiling_free_identity.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.tilingFamily
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
    owner := `D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam
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

abbrev seamSignature : Signature where
  Params := ℕ × (ℕ × ℕ)
  State _ := ℕ × ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def seamActual : Realization seamSignature :=
  realize seamSignature (fun _ p v => torusAdjacent p.1 p.2 v) (fun e => nomatch e)

def seamRejected : Realization seamSignature :=
  realize seamSignature (fun _ p v => ¬ torusAdjacent p.1 p.2 v) (fun e => nomatch e)

def seamArena : Arena where
  signature := seamSignature
  Law r := ∀ {n : ℕ} (u v : ℕ × ℕ),
    (u.1 < n - 1 ∧ u.2 < n - 1) → (v.1 < n - 1 ∧ v.2 < n - 1) →
    (r.readout () (n, u) v ↔ freeAdjacent u v)

private theorem seamRejectedLaw : ¬ seamArena.Law seamRejected := by
  intro h
  have hf := @h 3 (0, 0) (0, 0) (by decide) (by decide)
  simp [seamRejected, realize, torusAdjacent, freeAdjacent] at hf

private theorem seamDependence : ObservationalDependence seamSignature seamActual := by
  intro i
  refine ⟨(3, (0, 0)), (0, 0), (1, 0), ?_⟩
  simp [seamActual, realize, torusAdjacent, gap]

def seamFamily : Registration seamArena (type_of% (@empty_seam_adjacency)) where
  actual := seamActual
  bridge := Iff.rfl
  variation := ⟨@empty_seam_adjacency, seamRejected, seamRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨seamRejected, ?_, rfl, seamRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e
      exact nomatch e
  dependence := seamDependence

abbrev logSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def logActual : Realization logSignature :=
  realize logSignature (fun _ _ n => Real.log (freeCount n : ℝ)) (fun e => nomatch e)

def logRejected : Realization logSignature :=
  realize logSignature (fun _ _ n => -(n : ℝ) ^ 2) (fun e => nomatch e)

def logArena : Arena where
  signature := logSignature
  Law r := ∃ s : ℝ, 0 ≤ s ∧ Filter.Tendsto
    (fun n : ℕ => r.readout () () n / (n : ℝ) ^ 2) Filter.atTop (nhds s)

private theorem logRejectedLaw : ¬ logArena.Law logRejected := by
  rintro ⟨s, hs, ht⟩
  change Filter.Tendsto (fun n : ℕ => -(n : ℝ) ^ 2 / (n : ℝ) ^ 2)
    Filter.atTop (nhds s) at ht
  have hb : Filter.Tendsto (fun n : ℕ => -(n : ℝ) ^ 2 / (n : ℝ) ^ 2)
      Filter.atTop (nhds (-1 : ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [Filter.eventually_gt_atTop 0] with n hn
    have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp [hn0]
  have heq : s = -1 := tendsto_nhds_unique ht hb
  norm_num [heq] at hs

private theorem logDependence : ObservationalDependence logSignature logActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  have h0 : freeCount 0 = 1 := by
    norm_num [freeCount, independentSets, board, Finset.range_add_one, Finset.filter_singleton]
  have h1 : freeCount 1 = 2 := by
    norm_num [freeCount, independentSets, board, freeAdjacent, gap,
      Finset.range_add_one, Finset.powerset_insert, Finset.filter_insert, Finset.filter_singleton,
      Finset.product_eq_biUnion, singleton_powerset]
  change Real.log (freeCount 0 : ℝ) ≠ Real.log (freeCount 1 : ℝ)
  rw [h0, h1]
  simpa only [Nat.cast_one, Nat.cast_ofNat, Real.log_one] using
    (ne_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))

def logFamily : Registration logArena (type_of% (@free_log_limit)) where
  actual := logActual
  bridge := Iff.rfl
  variation := ⟨@free_log_limit, logRejected, logRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨logRejected, ?_, rfl, logRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim (α := Unit) j i)).elim
    · intro e
      exact nomatch e
  dependence := logDependence

noncomputable def seamRegistration : Contract.Registration
    (@_root_.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.empty_seam_adjacency)
    (Realization seamSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.empty_seam_adjacency.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.seamFamily
  realizationSource := none
  generated := false
  arena := .source ⟨seamArena⟩
  objectArena := .source ⟨seamArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source seamArena ⟨seamFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some seamActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def logRegistration : Contract.Registration
    (@_root_.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.free_log_limit)
    (Realization logSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.free_log_limit.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam.logFamily
  realizationSource := none
  generated := false
  arena := .source ⟨logArena⟩
  objectArena := .source ⟨logArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source logArena ⟨logFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some logActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "arg", "fn", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.Pressure.ToroidalKingsEmptySeam
