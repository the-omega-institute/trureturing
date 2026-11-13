import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Mehat.OrthogonalityProducts
import Reg.Support.DependentFamily

namespace Reg.D5.S3.Arith.Mehat.OrthogonalityProducts

open _root_.D5.S3.Arith.Mehat.OrthogonalityProducts
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped BigOperators

noncomputable section
set_option autoImplicit false

abbrev signature : Signature where
  Params := Σ k : ℕ, Fin k → Matrix (Fin 3) (Fin 3) ℤ
  State p := Fin p.1 → Fin 3 × Fin 3
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p a => ∏ i, (p.2 i (a i).1 (a i).2) ^ 2)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ k : ℕ, 1 ≤ k →
    ∃ (A : Fin k → Matrix (Fin 3) (Fin 3) ℤ) (gamma : Fin k → ℤ),
      (∀ i, gamma i ≠ 0 ∧ A i * (A i)ᵀ = gamma i • (1 : Matrix (Fin 3) (Fin 3) ℤ)) ∧
      Function.Injective (fun p : Fin k → Fin 3 × Fin 3 => R.readout () ⟨k,A⟩ p)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨A,gamma,horth,hinj⟩ := h 1 (by decide)
  have he := hinj (a₁ := fun _ => (0,0)) (a₂ := fun _ => (0,1)) rfl
  have hf := congrArg (fun p => (p 0).2) he
  exact (by decide : (0 : Fin 3) ≠ 1) hf

def registration : Registration arena (type_of% @problem92) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨problem92, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact False.elim (h (Subsingleton.elim _ _))
    · intro e
      exact nomatch e
  dependence := by
    intro _
    refine ⟨⟨1,fun _ => !![0,1,0; 0,0,0; 0,0,0]⟩,
      (fun _ => (0,0)), (fun _ => (0,1)), ?_⟩
    norm_num [actual, realize, Fin.prod_univ_succ]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@problem92) (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Mehat.OrthogonalityProducts.problem92.audit
  realizationName := `Reg.D5.S3.Arith.Mehat.OrthogonalityProducts.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p a => ∏ i, (p.2 i (a i).1 (a i).2) ^ 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Mehat.OrthogonalityProducts
    definition := some {
      owner := `D5.S3.Arith.Mehat.OrthogonalityProducts
      name := `D5.S3.Arith.Mehat.OrthogonalityProducts.Problem92
      path := #[] }
    coordinates := #[0,2]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "arg", "arg", "body"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end
end Reg.D5.S3.Arith.Mehat.OrthogonalityProducts
