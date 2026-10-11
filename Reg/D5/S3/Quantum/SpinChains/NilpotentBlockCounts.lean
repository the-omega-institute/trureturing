import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.SpinChains.NilpotentBlockCounts
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.SpinChains.NilpotentBlockCounts

namespace Reg.D5.S3.Quantum.SpinChains.NilpotentBlockCounts

universe u v w

abbrev rankSignature : Signature where
  Params := Unit
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def rankActual : Realization rankSignature :=
  realize rankSignature (fun _ _ a b => a = b) (fun e => nomatch e)

def rankRejected : Realization rankSignature :=
  realize rankSignature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev rankArena : Arena where
  signature := rankSignature
  Law R := ∀ {K : Type u} {V : Type v}
    [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (N : Module.End K V) {j : ℕ} (_hj : 1 ≤ j),
    R.readout () () (blockCount N j : ℤ)
      ((Module.finrank K (LinearMap.range (N ^ (j - 1))) : ℤ) -
        2 * (Module.finrank K (LinearMap.range (N ^ j)) : ℤ) +
          (Module.finrank K (LinearMap.range (N ^ (j + 1))) : ℤ))

theorem rankActualLaw : rankArena.{u, v}.Law rankActual := by
  intro K V _ _ _ _ N j hj
  exact blockCount_rank_formula N hj

theorem rankRejectedLaw : ¬ rankArena.{u, v}.Law rankRejected := by
  intro law
  let K := ULift.{u} ℚ
  let V := ULift.{v} PUnit
  have bad := law (K := K) (V := V) (0 : Module.End K V) (j := 1) (by decide)
  simp [rankRejected, realize] at bad

theorem rankDependence : ObservationalDependence rankSignature rankActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro eq
  have h := congrFun eq 0
  change (0 = 0) = (1 = (0 : ℤ)) at h
  exact Int.one_ne_zero (h.mp rfl)

def rankFamily : Registration (rankArena.{u, v}) (type_of% @blockCount_rank_formula.{u, v}) where
  actual := rankActual
  bridge := Iff.rfl
  variation := ⟨rankActualLaw, rankRejected, rankRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rankRejected, ?_, rfl, rankRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := rankDependence

def rankRegistration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@blockCount_rank_formula.{u, v}) (Realization rankSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.NilpotentBlockCounts.rank.unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.NilpotentBlockCounts.rankFamily
  realizationSource := none
  generated := false
  arena := .source ⟨rankArena.{u, v}⟩
  objectArena := .source ⟨rankArena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source rankArena.{u, v} ⟨rankFamily.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rankSignature rankActual.readout rankActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.NilpotentBlockCounts
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev countSignature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def countActual : Realization countSignature :=
  realize countSignature (fun _ _ a b => a = b) (fun e => nomatch e)

def countRejected : Realization countSignature :=
  realize countSignature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev countArena : Arena where
  signature := countSignature
  Law R := ∀ {K : Type u} {V : Type v} {W : Type w}
    [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (N : Module.End K V) (N' : Module.End K W)
    (_hρ : ∀ r : ℕ,
      Module.finrank K (LinearMap.range (N ^ r)) =
        Module.finrank K (LinearMap.range (N' ^ r))),
    ∀ j : ℕ, R.readout () () (blockCount N j) (blockCount N' j)

theorem countActualLaw : countArena.{u, v, w}.Law countActual := by
  intro K V W _ _ _ _ _ _ _ N N' hρ
  exact blockCount_eq_of_range_finrank_eq N N' hρ

theorem countRejectedLaw : ¬ countArena.{u, v, w}.Law countRejected := by
  intro law
  let K := ULift.{u} ℚ
  let V := ULift.{v} PUnit
  let W := ULift.{w} PUnit
  have bad := law (K := K) (V := V) (W := W)
    (0 : Module.End K V) (0 : Module.End K W) (by
      intro r
      cases r with
      | zero =>
          have hV : LinearMap.range (1 : Module.End K V) = (⊤ : Submodule K V) := by
            rw [LinearMap.range_eq_top]
            exact Function.surjective_id
          have hW : LinearMap.range (1 : Module.End K W) = (⊤ : Submodule K W) := by
            rw [LinearMap.range_eq_top]
            exact Function.surjective_id
          rw [pow_zero, pow_zero, hV, hW, finrank_top, finrank_top]
          rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]
      | succ r =>
          have hV : LinearMap.range
              ((0 : Module.End K V) ^ (Nat.succ r)) = (⊥ : Submodule K V) := by
            rw [show (0 : Module.End K V) ^ (Nat.succ r) = 0 by simp [pow_succ],
              LinearMap.range_zero]
          have hW : LinearMap.range
              ((0 : Module.End K W) ^ (Nat.succ r)) = (⊥ : Submodule K W) := by
            rw [show (0 : Module.End K W) ^ (Nat.succ r) = 0 by simp [pow_succ],
              LinearMap.range_zero]
          rw [hV, hW, finrank_bot, finrank_bot]) 0
  simp [countRejected, realize] at bad

theorem countDependence : ObservationalDependence countSignature countActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro eq
  have h := congrFun eq 0
  change (0 = 0) = (1 = (0 : ℕ)) at h
  exact Nat.one_ne_zero (h.mp rfl)

def countFamily : Registration (countArena.{u, v, w})
    (type_of% @blockCount_eq_of_range_finrank_eq.{u, v, w}) where
  actual := countActual
  bridge := Iff.rfl
  variation := ⟨countActualLaw, countRejected, countRejectedLaw⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨countRejected, ?_, rfl, countRejectedLaw⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := countDependence

def countRegistration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@blockCount_eq_of_range_finrank_eq.{u, v, w}) (Realization countSignature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.SpinChains.NilpotentBlockCounts.count.unit
  realizationName := `Reg.D5.S3.Quantum.SpinChains.NilpotentBlockCounts.countFamily
  realizationSource := none
  generated := false
  arena := .source ⟨countArena.{u, v, w}⟩
  objectArena := .source ⟨countArena.{u, v, w}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source countArena.{u, v, w} ⟨countFamily.{u, v, w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize countSignature countActual.readout countActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.SpinChains.NilpotentBlockCounts
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms rankFamily
#print axioms rankRegistration
#print axioms countFamily
#print axioms countRegistration

end Reg.D5.S3.Quantum.SpinChains.NilpotentBlockCounts
