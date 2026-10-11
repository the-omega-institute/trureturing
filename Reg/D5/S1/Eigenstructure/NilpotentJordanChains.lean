import LeanInformationAuditInterface.Contract.Registration
import D5.S1.Eigenstructure.NilpotentJordanChains
import Reg.Support.DependentFamily
import Mathlib.Algebra.Field.ULift

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S1.Eigenstructure.NilpotentJordanChains
open Module

namespace Reg.D5.S1.Eigenstructure.NilpotentJordanChains

universe u v w

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ a b => a = b) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {K : Type u} {V : Type v} {ι : Type w}
    [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
    (f : Module.End K V) (s : ι → ℕ+)
    (b : Basis (Σ i, Fin (s i)) K V)
    (_hb : ∀ (m : ℕ) (i : ι) (j : Fin (s i)),
      (f ^ m) (b ⟨i, j⟩) =
        if h : j.val + m < s i then b ⟨i, ⟨j.val + m, h⟩⟩ else 0)
    (m : ℕ), R.readout () () (Module.finrank K (LinearMap.range (f ^ m)))
      (∑ i, ((s i : ℕ) - m))

theorem actual_law : arena.{u, v, w}.Law actual := by
  intro K V ι _ _ _ _ f s b hb m
  exact chain_basis_rank f s b hb m

theorem rejected_law : ¬ arena.{u, v, w}.Law rejected := by
  intro law
  let K := ULift.{u} ℚ
  let V := ULift.{v} PUnit
  let ι := ULift.{w} Empty
  let s : ι → ℕ+ := fun i => nomatch i.down
  let b : Basis (Σ i, Fin (s i)) K V := Basis.empty _
  have bad := law (0 : Module.End K V) s b (by
    intro m i j
    exact (isEmptyElim i : False).elim) 0
  exact bad

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro eq
  have h := congrFun eq 0
  change (0 = 0) = (1 = (0 : ℕ)) at h
  exact Nat.one_ne_zero (h.mp rfl)

def family : Registration arena.{u, v, w} (type_of% @chain_basis_rank.{u, v, w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    (@chain_basis_rank.{u, v, w}) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S1.Eigenstructure.NilpotentJordanChains.unit
  realizationName := `Reg.D5.S1.Eigenstructure.NilpotentJordanChains.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u, v, w}⟩
  objectArena := .source ⟨arena.{u, v, w}⟩
  catalog := Lean.Name.anonymous
  localNames := true
  realization := .source arena.{u, v, w} ⟨family.{u, v, w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S1.Eigenstructure.NilpotentJordanChains
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end Reg.D5.S1.Eigenstructure.NilpotentJordanChains
