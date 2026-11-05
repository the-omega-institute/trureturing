import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.AliabadiQuotientObstruction
import Mathlib.Algebra.Group.ULift
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace Reg.D5.S3.FiniteGroups.AliabadiQuotientObstruction

open _root_.D5.S3.FiniteGroups.AliabadiQuotientObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

/-- The multiset cardinality observation on arbitrary carrier types. -/
abbrev signature : Signature where
  Params := Type u
  State G := Multiset G
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature.{u} :=
  realize signature.{u} (fun _ _ A => A.card) (fun e => nomatch e)

/-- All group, finiteness, noncommutativity and two-bijection clauses are retained. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (G : Type u) [Group G] [Fintype G] (hna : ¬ IsMulCommutative G),
    ∃ A : Multiset G, R.readout () G A = Fintype.card G ∧
      (A.map (Abelianization.of : G → Abelianization G)).prod = 1 ∧
      ¬ ∃ b c : Fin (Fintype.card G) → G,
        Function.Bijective b ∧ Function.Bijective c ∧
          A = Finset.univ.val.map (fun i => b i * (c i)⁻¹)

private theorem actual_law : arena.{u}.Law actual :=
  exists_obstructed_multiset

noncomputable def rejected : Realization signature.{u} :=
  realize signature.{u} (fun _ _ _ => 0) (fun e => nomatch e)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let G := ULift.{u} (Equiv.Perm (Fin 3))
  have hna : ¬ IsMulCommutative G := by
    intro hc
    have he := (isMulCommutative_iff.mp hc)
      (⟨Equiv.swap 0 1⟩ : G) (⟨Equiv.swap 1 2⟩ : G)
    have hv := congrArg (fun p : G => p.down 0) he
    norm_num [G, Equiv.Perm.mul_apply, Equiv.swap_apply_def] at hv
  obtain ⟨A, hcard, _⟩ := h G hna
  change 0 = Fintype.card G at hcard
  exact (Nat.ne_of_gt (Fintype.card_pos (α := G))) hcard.symm

noncomputable def sourceRegistration : Registration arena.{u}
    (type_of% @exists_obstructed_multiset.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := by
    intro role
    refine ⟨ULift.{u} Unit, 0, {⟨()⟩}, ?_⟩
    change (0 : Multiset (ULift.{u} Unit)).card ≠ ({⟨()⟩} : Multiset (ULift.{u} Unit)).card
    simp

noncomputable def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@exists_obstructed_multiset.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `D5.S3.FiniteGroups.AliabadiQuotientObstruction.exists_obstructed_multiset.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.AliabadiQuotientObstruction.sourceRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨sourceRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ A => A.card) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.AliabadiQuotientObstruction
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.AliabadiQuotientObstruction
