import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular
import Reg.Support.DependentFamily

/-! Typed coefficient observations for cycle length partitions. -/

namespace Reg.D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular
open _root_.D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open PowerSeries
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

#print axioms partitionAudit

end

end Reg.D5.S3.Combinatorics.Graph.RegularCHS.TwoRegular
