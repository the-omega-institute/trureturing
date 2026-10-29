import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Transport.StarGraphEvolutionMapsUnitarilySimilar
import Reg.Support.DependentFamily

/-! Source-bound audit of the unitary similarity of the two star-graph evolution maps. -/

namespace Reg.D5.S3.Quantum.Transport.StarGraphEvolutionMapsUnitarilySimilar

open _root_.D5.S3.Quantum.Transport.StarGraphEvolutionMapsUnitarilySimilar
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe equality of the two evolution matrices at each graph size. -/
abbrev signature : Signature where
  Params := ℕ
  State n := Matrix (Fin (n - 1) × Fin 2) (Fin (n - 1) × Fin 2) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := Matrix (Fin (n - 1) × Fin 2) (Fin (n - 1) × Fin 2) ℂ → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- Retain every parameter, the size hypothesis, and the unitary conjugating witness. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, 2 ≤ n → ∀ (r : Fin (n - 1) → ℂ) (r1 t1 : ℂ) (k : ℝ)
    (ℓ : Fin (n - 1) → ℝ),
    ∃ w ∈ Matrix.unitaryGroup (Fin (n - 1) × Fin 2) ℂ,
      R.readout () n (w * (scatteringMatrix r r1 t1 * propagationMatrix k ℓ) * star w)
        (propagationMatrix k ℓ * scatteringMatrix r r1 t1)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨w, _, hbad⟩ := h 2 (by decide) (fun _ => 0) 0 0 0 (fun _ => 0)
  exact hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 0, 1, ?_⟩
  intro he
  have hbad : (1 : Matrix (Fin (2 - 1) × Fin 2) (Fin (2 - 1) × Fin 2) ℂ) = 0 :=
    Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hbad

def source_registration : Registration arena claim where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Quantum.Transport.StarGraphEvolutionMapsUnitarilySimilar.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Transport.StarGraphEvolutionMapsUnitarilySimilar.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Transport.StarGraphEvolutionMapsUnitarilySimilar.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Transport.StarGraphEvolutionMapsUnitarilySimilar
    definition := some {
      owner := `D5.S3.Quantum.Transport.StarGraphEvolutionMapsUnitarilySimilar
      name := `D5.S3.Quantum.Transport.StarGraphEvolutionMapsUnitarilySimilar.claim
      path := #[] }
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Transport.StarGraphEvolutionMapsUnitarilySimilar
