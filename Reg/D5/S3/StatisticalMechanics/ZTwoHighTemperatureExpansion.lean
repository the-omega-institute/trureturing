import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.Algebra.Ring.ULift
import D5.S3.StatisticalMechanics.ZTwoHighTemperatureExpansion

/-! Source-bound registration for the high-temperature expansion over `𝔽₂`. The record
selects the sign `sgn R` applied to the parity `c ⬝ᵥ σ` of the inserted loop, read out as a
function `ZMod 2 → R` over the commutative ring `R` with its ring structure. Every other
clause, including the plaquette signs, is kept verbatim. -/

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.StatisticalMechanics.ZTwoHighTemperatureExpansion
open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.StatisticalMechanics.ZTwoHighTemperatureExpansion

universe u v w

noncomputable section

abbrev signature : Signature where
  Params := Σ R : Type u, CommRing R
  State _ := ZMod 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p z =>
    letI := p.2
    sgn p.1 z) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ =>
    letI := p.2
    (0 : p.1)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law r := ∀ {R : Type u} [ring : CommRing R] {E : Type v} {P : Type w} [Fintype E]
    [DecidableEq E] [Fintype P] [DecidableEq P] (M : Matrix P E (ZMod 2)) (t : P → R)
    (c : E → ZMod 2),
    ∑ σ : E → ZMod 2, r.readout () ⟨R, ring⟩ (c ⬝ᵥ σ) *
        ∏ p, (1 + t p * sgn R ((M *ᵥ σ) p)) =
      2 ^ Fintype.card E *
        ∑ S ∈ Finset.univ.filter (fun S : P → ZMod 2 => Mᵀ *ᵥ S = c),
          ∏ p ∈ Finset.univ.filter (fun p => S p ≠ 0), t p

private theorem rejected_law : ¬ arena.{u, v, w}.Law rejected := by
  intro h
  have hh := h (R := ULift.{u} ℤ) (E := PEmpty.{v + 1}) (P := PEmpty.{w + 1}) 0 (fun _ => 1) 0
  have hone : (1 : ULift.{u} ℤ) ≠ 0 := by
    intro h1
    have := congrArg ULift.down h1
    simp at this
  apply hone
  simpa [rejected, realize, Finset.filter_true_of_mem, Subsingleton.elim _ (0 : PEmpty.{w + 1} → ZMod 2)]
    using hh.symm

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨⟨ULift.{u} ℤ, inferInstance⟩, 0, 1, ?_⟩
  change sgn (ULift.{u} ℤ) 0 ≠ sgn (ULift.{u} ℤ) 1
  intro h
  have := congrArg ULift.down h
  simp [sgn] at this

def source : Registration arena.{u, v, w}
    (type_of% @sum_sgn_mul_prod_one_add_eq.{u, v, w}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@sum_sgn_mul_prod_one_add_eq.{u, v, w}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@sum_sgn_mul_prod_one_add_eq.{u, v, w}) (type_of% actual.{u}) Unit Unit := {
  unitName := `Reg.D5.S3.StatisticalMechanics.ZTwoHighTemperatureExpansion.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.ZTwoHighTemperatureExpansion.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.ZTwoHighTemperatureExpansion
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "arg", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms registration

end

end Reg.D5.S3.StatisticalMechanics.ZTwoHighTemperatureExpansion
