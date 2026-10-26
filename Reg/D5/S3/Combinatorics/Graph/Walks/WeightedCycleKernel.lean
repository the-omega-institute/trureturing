import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Combinatorics.Graph.Walks.WeightedCycleKernel
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

namespace Reg.D5.S3.Combinatorics.Graph.Walks.WeightedCycleKernel
open _root_.D5.S3.Combinatorics.Graph.Walks.WeightedCycleKernel
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped BigOperators Classical
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u

abbrev signature : Signature where
  Params := Σ _K : Type u, ℕ
  State p := Fin (p.2 + 1) → p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin (p.2 + 1) → p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ r => r) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ r => fun _ => r 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law s := ∀ {K : Type u} [Field K] {n : ℕ} (r : Fin (n + 1) → K),
    Module.finrank K (LinearMap.ker (transport (s.readout () ⟨K, n⟩ r))) =
      if ∏ i, r i = 1 then 1 else 0

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let r : Fin 2 → ULift.{u} ℚ := fun i => if i = 0 then 1 else 2
  have hh := @h (ULift.{u} ℚ) inferInstance 1 r
  rw [transport_nullity] at hh
  norm_num [rejected, realize, r, Fin.prod_univ_two] at hh
  change (∏ x : Fin 2, if x = 0 then (1 : ULift.{u} ℚ) else 2) = 1 at hh
  rw [Fin.prod_univ_two] at hh
  have hc := congrArg ULift.down hh
  norm_num at hc

private theorem dependence : ObservationalDependence signature.{u} actual := by
  classical
  intro i
  refine ⟨⟨ULift.{u} ℚ, 0⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hh := congrFun h 0
  exact zero_ne_one hh

def source_registration : Registration arena.{u} (type_of% @transport_nullity.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨transport_nullity, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@transport_nullity.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.WeightedCycleKernel.transport
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.WeightedCycleKernel.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ r => r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.WeightedCycleKernel
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
abbrev rankSignature : Signature where
  Params := Σ K : Type u, Σ n : ℕ, Fin (n + 1) → K
  State p := Fin (p.2.1 + 1) → p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Fin (p.2.1 + 1) → p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def rankActual : Realization rankSignature.{u} :=
  realize rankSignature (fun _ _ b => b) (fun e => nomatch e)

def rankRejected : Realization rankSignature.{u} :=
  realize rankSignature (fun _ p _ => p.2.2) (fun e => nomatch e)

abbrev rankArena : Arena where
  signature := rankSignature.{u}
  Law s := ∀ {K : Type u} [Field K] {n : ℕ} [CharP K 2]
    (a b : Fin (n + 1) → K) (hb : ∀ i, b i ≠ 0),
    (Matrix.fromBlocks 0 (cyclicBidiagonal a (s.readout () ⟨K, n, a⟩ b))
      (cyclicBidiagonal a b)ᵀ 0).rank =
      if ∏ i, a i = ∏ i, b i then 2 * n else 2 * (n + 1)

private theorem rankRejected_law : ¬ rankArena.{u}.Law rankRejected := by
  classical
  intro h
  let a : Fin 1 → ULift.{u} (ZMod 2) := fun _ => 0
  let b : Fin 1 → ULift.{u} (ZMod 2) := fun _ => 1
  have hb : ∀ i, b i ≠ 0 := by simp [b]
  have hh := @h (ULift.{u} (ZMod 2)) inferInstance 0 inferInstance a b hb
  let M := Matrix.fromBlocks 0 (cyclicBidiagonal a a) (cyclicBidiagonal a b)ᵀ 0
  have hrank : M.rank = Fintype.card (Fin 1 ⊕ Fin 1) := by
    simpa [M, rankRejected, realize, a, b] using hh
  obtain ⟨x, hx⟩ := Matrix.mulVec_surjective_iff_rank_eq_card.mpr hrank (fun _ => 1)
  have hz : cyclicBidiagonal a a = 0 := by funext i j; simp [cyclicBidiagonal, a]
  have hc := congrFun hx (Sum.inl 0)
  change (M *ᵥ x) (Sum.inl 0) = 1 at hc
  simp only [M, hz, Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, zero_add,
    Sum.elim_inl, Pi.zero_apply] at hc
  exact zero_ne_one hc

private theorem rankDependence : ObservationalDependence rankSignature.{u} rankActual := by
  classical
  intro i
  refine ⟨⟨ULift.{u} (ZMod 2), 0, fun _ => 1⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have hh := congrFun h 0
  exact zero_ne_one hh

def rankSource : Registration rankArena.{u} (type_of% @cyclic_bipartite_rank.{u}) where
  actual := rankActual
  bridge := Iff.rfl
  variation := ⟨cyclic_bipartite_rank, rankRejected, rankRejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rankRejected, ?_, rfl, rankRejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := rankDependence

def rankRegistration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@cyclic_bipartite_rank.{u}) (Realization rankSignature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Combinatorics.Graph.Walks.WeightedCycleKernel.rank
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Walks.WeightedCycleKernel.rankSource
  realizationSource := none
  generated := false
  arena := .source ⟨rankArena.{u}⟩
  objectArena := .source ⟨rankArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rankArena.{u} ⟨rankSource.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rankSignature.{u} (fun _ _ b => b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Walks.WeightedCycleKernel
    definition := none
    coordinates := #[0, 2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "fn", "fn", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms rankSource
#print axioms rankRegistration

end
end Reg.D5.S3.Combinatorics.Graph.Walks.WeightedCycleKernel
