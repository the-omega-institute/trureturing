import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.RegularCHS.Cubic
import Reg.Support.DependentFamily

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
open Classical
open scoped BigOperators
namespace Reg.D5.S3.Combinatorics.Graph.RegularCHS.Cubic
open _root_.D5.S3.Combinatorics.Graph.RegularCHS.Cubic
open _root_.D5.S3.Combinatorics.Graph.RegularCHS.Interface
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature where
  Params := Σ n : ℕ, SimpleGraph (Fin n)
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def evenActual : Realization signature :=
  realize signature (fun _ p j => closedWalks p.2 (2 * j)) (fun e => nomatch e)

def walkActual : Realization signature :=
  realize signature (fun _ p k => closedWalks p.2 k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev degreeArena : Arena where
  signature := signature
  Law R := ∀ {n r : ℕ} (G : SimpleGraph (Fin n))
    (_hr : ∀ v, r ≤ G.degree v) (j : ℕ),
    n * r ^ j ≤ R.readout () ⟨n, G⟩ j

private theorem degreeRejected : ¬ degreeArena.Law rejected := by
  intro h
  have he := @h 1 0 ⊥ (fun _ => Nat.zero_le _) 0
  change 1 * 0 ^ 0 ≤ 0 at he
  norm_num at he

private theorem secondCount {n : ℕ} (G : SimpleGraph (Fin n)) :
    closedWalks G 2 = ∑ v, G.degree v := by
  simp only [closedWalks, pow_two, SimpleGraph.adjMatrix_mul_self_apply_self, Nat.cast_id]

private theorem completeDegree {n : ℕ} (v : Fin n) :
    (fun G : SimpleGraph (Fin n) => G.degree v) ⊤ = n - 1 := by
  simpa only [← SimpleGraph.ncard_neighborSet, Fintype.card_fin] using
    (SimpleGraph.IsRegularOfDegree.top (V := Fin n) v)

private theorem completeSecond (n : ℕ) :
    closedWalks (⊤ : SimpleGraph (Fin n)) 2 = n * (n - 1) := by
  rw [secondCount]
  simp only [completeDegree, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul]

private theorem evenDependence : ObservationalDependence signature evenActual := by
  intro i
  refine ⟨⟨3, ⊤⟩, 0, 1, ?_⟩
  change closedWalks (⊤ : SimpleGraph (Fin 3)) 0 ≠ closedWalks ⊤ 2
  rw [completeSecond]
  norm_num [closedWalks, Matrix.one_apply]

def degreeSource : Registration degreeArena (type_of% @closedWalks_ge_of_minDegree) where
  actual := evenActual
  bridge := Iff.rfl
  variation := ⟨closedWalks_ge_of_minDegree, rejected, degreeRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, degreeRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := evenDependence

def degreeAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@closedWalks_ge_of_minDegree) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Cubic.degreeUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Cubic.degreeSource
  realizationSource := none
  generated := false
  arena := .source ⟨degreeArena⟩
  objectArena := .source ⟨degreeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source degreeArena ⟨degreeSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p j => closedWalks p.2 (2 * j)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.RegularCHS.Cubic
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

abbrev cubicArena : Arena where
  signature := signature
  Law R := ∀ {n : ℕ} (G : SimpleGraph (Fin n)) (_hn : 3 ≤ n)
    (_hr : G.IsRegularOfDegree 3) (k : ℕ) (_hk : 1 ≤ k),
    closedWalks (SimpleGraph.cycleGraph n) k ≤ R.readout () ⟨n, G⟩ k

private theorem cubicRejected : ¬ cubicArena.Law rejected := by
  intro h
  have hr : (fun G : SimpleGraph (Fin 4) => G.IsRegularOfDegree 3) ⊤ := by
    intro v
    exact completeDegree v
  have he := @h 4 ⊤ (by omega) hr 2 (by omega)
  change closedWalks (SimpleGraph.cycleGraph 4) 2 ≤ 0 at he
  have hc : closedWalks (SimpleGraph.cycleGraph 4) 2 = 8 := by
    have hd : ∀ v : Fin 4,
        (fun G : SimpleGraph (Fin 4) => G.degree v) (SimpleGraph.cycleGraph 4) = 2 := by
      intro v
      simpa only [← SimpleGraph.ncard_neighborSet] using
        (SimpleGraph.cycleGraph_degree_three_le (n := 1) (v := v))
    rw [secondCount]
    simp only [hd, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

private theorem walkDependence : ObservationalDependence signature walkActual := by
  intro i
  refine ⟨⟨4, ⊤⟩, 1, 2, ?_⟩
  change closedWalks (⊤ : SimpleGraph (Fin 4)) 1 ≠ closedWalks ⊤ 2
  rw [completeSecond]
  norm_num [closedWalks]

def cubicSource : Registration cubicArena (type_of% @closedWalks_cubic_ge_cycle) where
  actual := walkActual
  bridge := Iff.rfl
  variation := ⟨closedWalks_cubic_ge_cycle, rejected, cubicRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, cubicRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := walkDependence

def cubicAudit : LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@closedWalks_cubic_ge_cycle) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Cubic.cubicUnit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.RegularCHS.Cubic.cubicSource
  realizationSource := none
  generated := false
  arena := .source ⟨cubicArena⟩
  objectArena := .source ⟨cubicArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source cubicArena ⟨cubicSource⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p k => closedWalks p.2 k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.RegularCHS.Cubic
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms degreeAudit
#print axioms cubicAudit

end Reg.D5.S3.Combinatorics.Graph.RegularCHS.Cubic
