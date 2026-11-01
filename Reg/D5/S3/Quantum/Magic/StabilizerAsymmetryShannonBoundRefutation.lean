import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Magic.StabilizerAsymmetryShannonBoundRefutation
import Reg.Support.DependentFamily

/-! Source-bound audit of the eight-word binary sum identity. -/

namespace Reg.D5.S3.Quantum.Magic.StabilizerAsymmetryShannonBoundRefutation

open _root_.D5.S3.Quantum.Magic.StabilizerAsymmetryShannonBoundRefutation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

namespace SumBits

/-- Observe the summand at the first binary word. -/
abbrev signature : Signature where
  Params := Type u
  State α := (Fin 3 → ZMod 2) → α
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ α := α
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ f => f ![0, 0, 0]) (fun e => Empty.elim e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ f => f ![1, 1, 1]) (fun e => Empty.elim e)

/-- Retain the full additive-monoid identity, replacing only its first summand. -/
abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {α : Type u} [AddCommMonoid α] (f : (Fin 3 → ZMod 2) → α),
    (∑ x, f x) = r.readout () α f + f ![0, 0, 1] +
      f ![0, 1, 0] + f ![0, 1, 1] + f ![1, 0, 0] +
      f ![1, 0, 1] + f ![1, 1, 0] + f ![1, 1, 1]

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have he := @h (ULift.{u} ℕ) inferInstance
    (fun x => if x 0 = 0 then 0 else 1)
  rw [sum_bits] at he
  have hd := congrArg ULift.down he
  norm_num [rejected, realize] at hd

theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} ℕ, (fun _ => 0), (fun _ => 1), ?_⟩
  intro he
  have hd := congrArg ULift.down he
  exact Nat.zero_ne_one hd

def source : Registration arena.{u} (type_of% @sum_bits.{u}) where
  actual := realize signature.{u}
    (fun _ _ f => f ![0, 0, 0]) (fun e => Empty.elim e)
  bridge := Iff.rfl
  variation := ⟨sum_bits, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@sum_bits.{u}) (Realization signature.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Magic.StabilizerAsymmetryShannonBoundRefutation.SumBits.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Magic.StabilizerAsymmetryShannonBoundRefutation.SumBits.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ _ f => f ![0, 0, 0]) (fun e => Empty.elim e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Magic.StabilizerAsymmetryShannonBoundRefutation
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg", "fn", "arg", "fn", "arg",
        "fn", "arg", "fn", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

set_option pp.proofs false in
#print sum_bits
#print axioms source
#print axioms registration

end SumBits

end
end Reg.D5.S3.Quantum.Magic.StabilizerAsymmetryShannonBoundRefutation
