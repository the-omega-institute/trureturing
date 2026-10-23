import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Walks.WeightedPathCycleRank
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

namespace Reg.D5.S3.Combinatorics.Graph.Walks.WeightedPathCycleRank
open _root_.D5.S3.Combinatorics.Graph.Walks.WeightedPathCycleRank
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators Classical
open SimpleGraph Matrix
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v

abbrev signature : Signature where
  Params := Σ _V : Type u, Type v
  State p := Matrix p.1 p.1 p.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix p.1 p.1 p.2
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v} :=
  realize signature (fun _ _ A => A) (fun e => nomatch e)

def rejected : Realization signature.{u,v} :=
  realize signature (fun _ _ A => fun i _ => A i i) (fun e => nomatch e)

abbrev pathArena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {V : Type u} {K : Type v} [Fintype V] [Field K] [CharP K 2]
    {m : ℕ} (A : Matrix V V K) (hs : A.IsSymm) (hd : ∀ i, A i i = 0)
    (e : Fin m ≃ V) (he : ∀ i j, (pathGraph m).Adj i j ↔ A (e i) (e j) ≠ 0),
    (r.readout () ⟨V, K⟩ A).rank = 2 * (m / 2)

private theorem pathRejected : ¬ pathArena.{u,v}.Law rejected := by
  classical
  intro h
  let G : SimpleGraph (ULift.{u} (Fin 2)) := (pathGraph 2).comap ULift.down
  let A : Matrix (ULift.{u} (Fin 2)) (ULift.{u} (Fin 2)) (ULift.{v} (ZMod 2)) := G.adjMatrix _
  have hs : A.IsSymm := G.isSymm_adjMatrix
  have hd : ∀ i, A i i = 0 := by intro i; simp [A]
  have he : ∀ i j, (pathGraph 2).Adj i j ↔
      A (ULift.up i) (ULift.up j) ≠ 0 := by intro i j; simp [A, G]
  have hh := @h _ _ inferInstance inferInstance inferInstance 2 A hs hd Equiv.ulift.symm he
  have hz : rejected.readout () ⟨_, _⟩ A = 0 := by
    funext i j
    exact hd i
  rw [hz, Matrix.rank_zero] at hh
  norm_num at hh

private theorem dependence : ObservationalDependence signature.{u,v} actual := by
  classical
  intro i
  refine ⟨⟨ULift.{u} (Fin 1), ULift.{v} (ZMod 2)⟩, 0, 1, ?_⟩
  intro h
  have hh := congrArg (fun M : Matrix (ULift.{u} (Fin 1)) (ULift.{u} (Fin 1))
    (ULift.{v} (ZMod 2)) => M ⟨0⟩ ⟨0⟩) h
  change (0 : ULift.{v} (ZMod 2)) = 1 at hh
  exact zero_ne_one hh

def pathSource : Registration pathArena.{u,v} (type_of% @rank_path.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rank_path, rejected, pathRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, pathRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

abbrev oddArena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {V : Type u} {K : Type v} [Fintype V] [Field K] [CharP K 2]
    {m : ℕ} (hm : 3 ≤ m) (ho : Odd m) (A : Matrix V V K)
    (hs : A.IsSymm) (hd : ∀ i, A i i = 0)
    (e : Fin m ≃ V) (he : ∀ i j, (cycleGraph m).Adj i j ↔ A (e i) (e j) ≠ 0),
    (r.readout () ⟨V, K⟩ A).rank = m - 1

private theorem oddRejected : ¬ oddArena.{u,v}.Law rejected := by
  classical
  intro h
  let G : SimpleGraph (ULift.{u} (Fin 3)) := (cycleGraph 3).comap ULift.down
  let A : Matrix (ULift.{u} (Fin 3)) (ULift.{u} (Fin 3)) (ULift.{v} (ZMod 2)) := G.adjMatrix _
  have hs : A.IsSymm := G.isSymm_adjMatrix
  have hd : ∀ i, A i i = 0 := by intro i; simp [A]
  have he : ∀ i j, (cycleGraph 3).Adj i j ↔
      A (ULift.up i) (ULift.up j) ≠ 0 := by intro i j; simp [A, G]
  have hh := @h _ _ inferInstance inferInstance inferInstance 3 (by omega) (by decide)
    A hs hd Equiv.ulift.symm he
  have hz : rejected.readout () ⟨_, _⟩ A = 0 := by
    funext i j
    exact hd i
  rw [hz, Matrix.rank_zero] at hh
  norm_num at hh

def oddSource : Registration oddArena.{u,v} (type_of% @rank_odd_cycle.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rank_odd_cycle, rejected, oddRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, oddRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

abbrev evenArena : Arena where
  signature := signature.{u,v}
  Law r := ∀ {V : Type u} {K : Type v} [Fintype V] [Field K] [CharP K 2]
    {n : ℕ} (A : Matrix V V K) (hs : A.IsSymm)
    (G : SimpleGraph V) (he : ∀ u v, G.Adj u v ↔ A u v ≠ 0)
    (e : evenCycleGraph n ≃g G),
    (r.readout () ⟨V, K⟩ A).rank =
      if (∏ i, A (e (Sum.inl i)) (e (Sum.inr i))) =
        ∏ i, A (e (Sum.inl i)) (e (Sum.inr (finRotate (n + 2) i)))
      then 2 * n + 2 else 2 * (n + 2)

private theorem evenRejected : ¬ evenArena.{u,v}.Law rejected := by
  classical
  intro h
  let G : SimpleGraph (ULift.{u} (Fin 2 ⊕ Fin 2)) := (evenCycleGraph 0).comap ULift.down
  let e : evenCycleGraph 0 ≃g G := (SimpleGraph.Iso.comap Equiv.ulift (evenCycleGraph 0)).symm
  let A : Matrix (ULift.{u} (Fin 2 ⊕ Fin 2)) (ULift.{u} (Fin 2 ⊕ Fin 2))
      (ULift.{v} (ZMod 2)) := G.adjMatrix _
  have hs : A.IsSymm := G.isSymm_adjMatrix
  have he : ∀ i j, G.Adj i j ↔ A i j ≠ 0 := by intro i j; simp [A]
  have h₁ (i : Fin 2) : A (e (Sum.inl i)) (e (Sum.inr i)) = 1 := by
    have hh : (evenCycleGraph 0).Adj (Sum.inl i) (Sum.inr i) := Or.inl rfl
    simp only [A, adjMatrix_apply, e.map_adj_iff.mpr hh, ite_true]
  have h₂ (i : Fin 2) : A (e (Sum.inl i)) (e (Sum.inr (finRotate 2 i))) = 1 := by
    have hh : (evenCycleGraph 0).Adj (Sum.inl i) (Sum.inr (finRotate 2 i)) := Or.inr rfl
    simp only [A, adjMatrix_apply, e.map_adj_iff.mpr hh, ite_true]
  have hh := @h _ _ inferInstance inferInstance inferInstance 0 A hs G he e
  have hz : rejected.readout () ⟨_, _⟩ A = 0 := by
    funext i j
    change A i i = 0
    simp [A]
  rw [hz, Matrix.rank_zero] at hh
  simp only [h₁, h₂, Finset.prod_const_one, ite_true] at hh
  norm_num at hh

def evenSource : Registration evenArena.{u,v} (type_of% @rank_even_cycle.{u,v}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨rank_even_cycle, rejected, evenRejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, evenRejected⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def pathRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rank_path.{u,v}) (Realization signature.{u,v}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.WeightedPathCycleRank.path
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.WeightedPathCycleRank.pathSource
  realizationSource := none
  generated := false
  arena := .source ⟨pathArena.{u,v}⟩
  objectArena := .source ⟨pathArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pathArena.{u,v} ⟨pathSource.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v} (fun _ _ A => A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.WeightedPathCycleRank
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms pathSource
#print axioms pathRegistration

def oddRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rank_odd_cycle.{u,v}) (Realization signature.{u,v}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.WeightedPathCycleRank.odd
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.WeightedPathCycleRank.oddSource
  realizationSource := none
  generated := false
  arena := .source ⟨oddArena.{u,v}⟩
  objectArena := .source ⟨oddArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source oddArena.{u,v} ⟨oddSource.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v} (fun _ _ A => A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.WeightedPathCycleRank
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 8
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms oddSource
#print axioms oddRegistration

def evenRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rank_even_cycle.{u,v}) (Realization signature.{u,v}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.WeightedPathCycleRank.even
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.WeightedPathCycleRank.evenSource
  realizationSource := none
  generated := false
  arena := .source ⟨evenArena.{u,v}⟩
  objectArena := .source ⟨evenArena.{u,v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source evenArena.{u,v} ⟨evenSource.{u,v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u,v} (fun _ _ A => A) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.WeightedPathCycleRank
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms evenSource
#print axioms evenRegistration

abbrev adjacencySignature : Signature where
  Params := Type u
  State V := SimpleGraph V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ V := SimpleGraph V
  Anchor := Empty
  finiteAnchor := inferInstance

def adjacencyActual : Realization adjacencySignature.{u} :=
  realize adjacencySignature (fun _ _ G => G) (fun e => nomatch e)

def adjacencyRejected : Realization adjacencySignature.{u} :=
  realize adjacencySignature (fun _ _ _ => ⊥) (fun e => nomatch e)

abbrev adjacencyArena : Arena where
  signature := adjacencySignature.{u}
  Law r := ∀ {V : Type u} [Fintype V] {n : ℕ}
    (G : SimpleGraph V) (e : evenCycleGraph n ≃g G),
    ((r.readout () V G).adjMatrix (ZMod 2)).rank = 2 * n + 2

private theorem adjacencyBad : ¬ adjacencyArena.{u}.Law adjacencyRejected := by
  classical
  intro h
  let G : SimpleGraph (ULift.{u} (Fin 2 ⊕ Fin 2)) := (evenCycleGraph 0).comap ULift.down
  let e : evenCycleGraph 0 ≃g G := (SimpleGraph.Iso.comap Equiv.ulift (evenCycleGraph 0)).symm
  have hh := @h (ULift.{u} (Fin 2 ⊕ Fin 2)) inferInstance 0 G e
  have hz : (adjacencyRejected.readout () (ULift.{u} (Fin 2 ⊕ Fin 2)) G).adjMatrix
      (ZMod 2) = 0 := by
    ext i j
    simp [adjMatrix_apply, adjacencyRejected, realize]
  rw [hz, Matrix.rank_zero] at hh
  norm_num at hh

private theorem adjacencyDependence : ObservationalDependence adjacencySignature.{u} adjacencyActual := by
  classical
  intro i
  refine ⟨ULift.{u} (Fin 2), ⊥, ⊤, ?_⟩
  intro h
  change (⊥ : SimpleGraph (ULift.{u} (Fin 2))) = ⊤ at h
  have hh := congrArg (fun G : SimpleGraph (ULift.{u} (Fin 2)) => G.Adj ⟨0⟩ ⟨1⟩) h
  simp at hh

def adjacencySource : Registration adjacencyArena.{u} (type_of% @rank_even_adjacency.{u}) where
  actual := adjacencyActual
  bridge := Iff.rfl
  variation := ⟨rank_even_adjacency, adjacencyRejected, adjacencyBad⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨adjacencyRejected, ?_, rfl, adjacencyBad⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := adjacencyDependence

def adjacencyRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rank_even_adjacency.{u}) (Realization adjacencySignature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.WeightedPathCycleRank.adjacency
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.WeightedPathCycleRank.adjacencySource
  realizationSource := none
  generated := false
  arena := .source ⟨adjacencyArena.{u}⟩
  objectArena := .source ⟨adjacencyArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source adjacencyArena.{u} ⟨adjacencySource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize adjacencySignature.{u} (fun _ _ G => G) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.WeightedPathCycleRank
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "fn", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms adjacencySource
#print axioms adjacencyRegistration

end
end Reg.D5.S3.Combinatorics.Graph.Walks.WeightedPathCycleRank
