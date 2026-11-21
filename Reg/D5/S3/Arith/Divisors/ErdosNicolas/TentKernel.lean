import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Divisors.ErdosNicolas.TentKernel
import Reg.Support.DependentFamily

/-! Source-bound audit of the rational kernel quadratic form on arbitrary finite families. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Reg.D5.S3.Arith.Divisors.ErdosNicolas.TentKernel

open _root_.D5.S3.Arith.ErdosNicolas
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset
open scoped BigOperators

universe u
noncomputable section

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℚ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ L r => K L r) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} (S : Finset ι) (x : ι → ℤ) (c : ι → ℚ)
    {L : ℕ} (_ : 0 < L),
    0 ≤ ∑ i ∈ S, ∑ j ∈ S, c i * c j * R.readout () L (x i - x j).natAbs

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  classical
  intro h
  let j : ULift.{u} Unit := ⟨()⟩
  have he := h ({j} : Finset (ULift.{u} Unit)) (fun _ => 0) (fun _ => 1)
    (L := 1) (by decide)
  norm_num [rejected, realize] at he

def evidence : Registration arena.{u} (type_of% @kernel_psd.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@kernel_psd.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    norm_num [actual, realize, K]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@kernel_psd.{u}) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.ErdosNicolas.kernel_psd.__information_unit
  realizationName := `Reg.D5.S3.Arith.Divisors.ErdosNicolas.TentKernel.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := .anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ L r => K L r) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Divisors.ErdosNicolas.TentKernel
    definition := none
    coordinates := #[4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body",
        "arg", "arg", "body", "arg", "body", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms audit

end
end Reg.D5.S3.Arith.Divisors.ErdosNicolas.TentKernel
