import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.RegularRepresentation.RegularNormalizerSaturation
import Reg.Support.DependentFamily

/- Candidate Reg mirror; kernel compilation and source-binding validation are separate obligations.
   Original source SHA-256:
   6fa56fe4a9710fd892576d55c102ff191b4fb216f5e433dd8c48262e2036623b
   Only the single public saturation iff is an audit target here.

   One observation family is used: the actual Nat.card H occurring three
   times in the original right-hand side.  Its state is Type v, not a finite
   sample of groups.  The complete law retains independent u and v, Group H,
   Nonempty K, Finite H, both ambient subgroups and the square-one condition.
   A finite witness below only refutes an intervention; it does not replace
   the arbitrary source family.  No theorem-truth Bool is used.

   The readout head is the existing enrolled DependentFamily.realize from
   Reg.Support.DependentFamily.enrollment_1.
   Raw selector paths describe the intended Nat.card H source observations;
   their compilation does not establish validated source binding.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.FiniteGroups.RegularNormalizerSaturation

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.FiniteGroups

noncomputable section

abbrev cardinalSignature.{v} : Signature.{0, v + 1, 0, 0, 0} where
  Params := Unit
  State _ := Type v
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Nat
  Anchor := Empty
  finiteAnchor := inferInstance

def actualCard.{v} : Realization cardinalSignature.{v} :=
  realize cardinalSignature.{v}
    (fun _ _ H => Nat.card H) (fun e => nomatch e)

def rejectedCard.{v} : Realization cardinalSignature.{v} :=
  realize cardinalSignature.{v}
    (fun _ _ _ => 5) (fun e => nomatch e)

abbrev saturationArena.{u, v} : Arena.{0, v + 1, 0, 0, 0} where
  signature := cardinalSignature.{v}
  Law R := ∀ (K : Type u) (H : Type v) [Group H] [Nonempty K],
    DiagonalRegularNormalizer.diagonalNormalizer K H =
        UniformPartitionAutomorphisms.Aut K H ↔
      Finite H ∧ (R.readout () () H ≤ 2 ∨ (Subsingleton K ∧
        (R.readout () () H = 3 ∨
          (R.readout () () H = 4 ∧ ∀ h : H, h * h = 1))))

private theorem actual_law.{u, v} :
    saturationArena.{u, v}.Law actualCard.{v} := by
  exact @_root_.D5.S3.FiniteGroups.RegularNormalizerSaturation.diagonalNormalizer_eq_partitionAut_iff.{u, v}

private theorem rejected_law.{u, v} :
    ¬ saturationArena.{u, v}.Law rejectedCard.{v} := by
  intro h
  have hcard : Nat.card (PUnit.{v + 1}) ≤ 2 := by
    rw [Nat.card_unique]
    decide
  have heq :
      DiagonalRegularNormalizer.diagonalNormalizer (PUnit.{u + 1}) (PUnit.{v + 1}) =
        UniformPartitionAutomorphisms.Aut (PUnit.{u + 1}) (PUnit.{v + 1}) :=
    (_root_.D5.S3.FiniteGroups.RegularNormalizerSaturation.diagonalNormalizer_eq_partitionAut_iff
      (PUnit.{u + 1}) (PUnit.{v + 1})).mpr ⟨inferInstance, Or.inl hcard⟩
  have hclass := (h (PUnit.{u + 1}) (PUnit.{v + 1})).mp heq
  change Finite (PUnit.{v + 1}) ∧
    ((5 : Nat) ≤ 2 ∨ (Subsingleton (PUnit.{u + 1}) ∧
      (5 = 3 ∨ (5 = 4 ∧ ∀ x : PUnit.{v + 1}, x * x = 1)))) at hclass
  norm_num at hclass

def cardinalFamily.{u, v} : Registration saturationArena.{u, v}
    (type_of% @_root_.D5.S3.FiniteGroups.RegularNormalizerSaturation.diagonalNormalizer_eq_partitionAut_iff.{u, v}) where
  actual := actualCard.{v}
  bridge := Iff.rfl
  variation := ⟨actual_law.{u, v}, rejectedCard.{v}, rejected_law.{u, v}⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejectedCard.{v}, ?_, rfl, rejected_law.{u, v}⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), PUnit.{v + 1},
      Equiv.Perm (PUnit.{v + 1} ⊕ PUnit.{v + 1}), ?_⟩
    change Nat.card (PUnit.{v + 1}) ≠
      Nat.card (Equiv.Perm (PUnit.{v + 1} ⊕ PUnit.{v + 1}))
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm]

/- The four original outer binders are K, H, Group H and Nonempty K.
   Each proposed path targets its intended Nat.card H application, with H its
   final argument.
   Compiling these selectors does not certify source binding.
-/
def cardinalSelection : Contract.SourceSelection where
  owner := `D5.S3.FiniteGroups.RegularNormalizerSaturation
  definition := none
  coordinates := #[]
  readouts := #[
    { path := #["body", "body", "body", "body", "arg", "arg",
        "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false },
    { path := #["body", "body", "body", "body", "arg", "arg",
        "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false },
    { path := #["body", "body", "body", "body", "arg", "arg",
        "arg", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }]

def registration.{u, v} : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.FiniteGroups.RegularNormalizerSaturation.diagonalNormalizer_eq_partitionAut_iff.{u, v})
    (Realization cardinalSignature.{v}) (Type (v + 1)) Unit := {
  unitName := `D5.S3.FiniteGroups.RegularNormalizerSaturation.diagonalNormalizer_eq_partitionAut_iff.__information_unit
  realizationName := `Reg.D5.S3.FiniteGroups.RegularNormalizerSaturation.cardinalFamily
  realizationSource := none
  generated := false
  arena := .source ⟨saturationArena.{u, v}⟩
  objectArena := .source ⟨saturationArena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source saturationArena.{u, v} ⟨cardinalFamily.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize cardinalSignature.{v}
    (fun _ _ H => Nat.card H) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (Type v)
  sourceSelection := some cardinalSelection
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.FiniteGroups.RegularNormalizerSaturation
