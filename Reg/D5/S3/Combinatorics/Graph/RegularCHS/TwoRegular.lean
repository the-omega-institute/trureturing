import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular
import Reg.Support.DependentFamily

/-! Typed coefficient observations for cycle length partitions. -/

namespace Reg.D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular
open _root_.D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open PowerSeries Classical
noncomputable section

abbrev partitionSignature : Signature where
  Params := List ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def partitionActual : Realization partitionSignature :=
  realize partitionSignature (fun _ ls k => coeff k (ls.map cycleKernel).prod)
    (fun e => nomatch e)

def partitionRejected : Realization partitionSignature :=
  realize partitionSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev partitionArena : Arena where
  signature := partitionSignature
  Law R := ∀ (ls : List ℕ), ls ≠ [] → (∀ l ∈ ls, 0 < l) → ∀ k,
    coeff k (cycleKernel ls.sum) ≤ R.readout () ls k

private theorem partitionArenaRejected : ¬ partitionArena.Law partitionRejected := by
  intro h
  have he := h [1] (by simp) (by simp) 0
  norm_num [partitionRejected, realize, cycleKernel,
    coeff_subst_X_pow (by decide : (1 : ℕ) ≠ 0)] at he

private theorem partitionArenaDependence :
    ObservationalDependence partitionSignature partitionActual := by
  intro i
  refine ⟨[1], 0, 1, ?_⟩
  norm_num [partitionActual, realize, cycleKernel,
    coeff_subst_X_pow (by decide : (1 : ℕ) ≠ 0)]

def partitionArenaSource : Registration partitionArena
    (type_of% @cycleKernel_sum_le_prod) where
  actual := partitionActual
  bridge := Iff.rfl
  variation := ⟨cycleKernel_sum_le_prod, partitionRejected, partitionArenaRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨partitionRejected, ?_, rfl, partitionArenaRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := partitionArenaDependence

def partitionAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@cycleKernel_sum_le_prod) (Realization partitionSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular.partitionAuditUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular.partitionArenaSource
  realizationSource := none
  generated := false
  arena := .source ⟨partitionArena⟩
  objectArena := .source ⟨partitionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source partitionArena ⟨partitionArenaSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize partitionSignature
    (fun _ ls k => coeff k (ls.map cycleKernel).prod) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev twoRegularSignature : Signature where
  Params := Σ n : ℕ, SimpleGraph (Fin n)
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def twoRegularActual : Realization twoRegularSignature :=
  realize twoRegularSignature (fun _ p d => _root_.D5.S3.Combinatorics.Graph.RegularCHS.Defs.chs p.2 d) (fun e => nomatch e)

def twoRegularRejected : Realization twoRegularSignature :=
  realize twoRegularSignature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev twoRegularArena : Arena where
  signature := twoRegularSignature
  Law R := ∀ {n : ℕ}, 3 ≤ n → ∀ G : SimpleGraph (Fin n),
    G.IsRegularOfDegree 2 → ∀ d,
      _root_.D5.S3.Combinatorics.Graph.RegularCHS.Defs.chs (SimpleGraph.cycleGraph n) d ≤ R.readout () ⟨n, G⟩ d

private theorem twoRegularArenaRejected : ¬twoRegularArena.Law twoRegularRejected := by
  intro h
  have he := h (by decide : 3 ≤ 3) (SimpleGraph.cycleGraph 3) (by
    intro v
    simpa only [← SimpleGraph.ncard_neighborSet] using
      (SimpleGraph.cycleGraph_degree_three_le (n := 0) (v := v))) 0
  norm_num [twoRegularRejected, realize, _root_.D5.S3.Combinatorics.Graph.RegularCHS.Defs.chs, MvPolynomial.hsymm_zero] at he

private theorem twoRegularArenaDependence :
    ObservationalDependence twoRegularSignature twoRegularActual := by
  intro i
  refine ⟨⟨0, (⊥ : SimpleGraph (Fin 0))⟩, 0, 1, ?_⟩
  norm_num [twoRegularActual, realize, _root_.D5.S3.Combinatorics.Graph.RegularCHS.Defs.chs, MvPolynomial.hsymm_zero,
    MvPolynomial.hsymm_one]

def twoRegularArenaSource : Registration twoRegularArena
    (type_of% @chs_cycle_le_twoRegular) where
  actual := twoRegularActual
  bridge := Iff.rfl
  variation := ⟨chs_cycle_le_twoRegular, twoRegularRejected, twoRegularArenaRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨twoRegularRejected, ?_, rfl, twoRegularArenaRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := twoRegularArenaDependence

def twoRegularAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@chs_cycle_le_twoRegular) (Realization twoRegularSignature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular.twoRegularAuditUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular.twoRegularArenaSource
  realizationSource := none
  generated := false
  arena := .source ⟨twoRegularArena⟩
  objectArena := .source ⟨twoRegularArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source twoRegularArena ⟨twoRegularArenaSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize twoRegularSignature
    (fun _ p d => _root_.D5.S3.Combinatorics.Graph.RegularCHS.Defs.chs p.2 d) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms partitionAudit
#print axioms twoRegularAudit

end

end Reg.D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular
