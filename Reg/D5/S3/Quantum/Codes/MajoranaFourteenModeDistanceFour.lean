import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Codes.MajoranaFourteenModeDistanceFour
import Reg.Support.DependentFamily

/-! Source-bound audit of the strict weight bound for a logical Majorana operator. -/

namespace Reg.D5.S3.Quantum.Codes.MajoranaFourteenModeDistanceFour

open _root_.D5.S3.Quantum.Codes.MajoranaFourteenModeDistanceFour
open _root_.D5.S3.Fourier.CharacterSelection.BinaryCharacterCodeDuality
  (characterOrthogonalComplement)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the strict order relation on the weight and its natural-number bound. -/
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
  realize signature (fun _ _ x y => x < y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

/-- Retain the full code telescope and both membership conditions on the witness. -/
abbrev arena : Arena where
  signature := signature
  Law R := ∀ n : ℕ, n ≤ 14 → ∀ c : Submodule (ZMod 2) (Fin n → ZMod 2),
    IsSelfOrthogonal c → (fun _ => 1) ∈ c →
    2 * Module.finrank (ZMod 2) c < n →
    ∃ v ∈ characterOrthogonalComplement (ZMod 2) c,
      v ∉ c ∧ R.readout () () (hammingNorm v) 4

private def parityCode : Submodule (ZMod 2) (Fin 4 → ZMod 2) :=
  Submodule.span (ZMod 2) {(fun _ => 1)}

private theorem parityCode_selfOrthogonal : IsSelfOrthogonal parityCode := by
  intro x hx y hy
  rcases Submodule.mem_span_singleton.mp hx with ⟨a, rfl⟩
  rcases Submodule.mem_span_singleton.mp hy with ⟨b, rfl⟩
  rw [smul_dotProduct, dotProduct_smul]
  have hones : (fun _ : Fin 4 => (1 : ZMod 2)) ⬝ᵥ (fun _ => 1) = 0 := by decide
  simp only [hones, smul_zero]

private theorem parityCode_finrank : Module.finrank (ZMod 2) parityCode = 1 := by
  apply finrank_span_singleton
  intro h
  exact one_ne_zero (congrFun h 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨v, _, _, hfalse⟩ := h 4 (by decide) parityCode parityCode_selfOrthogonal
    (Submodule.mem_span_singleton_self _) (by rw [parityCode_finrank]; decide)
  exact hfalse

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  exact (lt_irrefl (1 : ℕ)) (Eq.mp (congrFun h 1) (by decide : (0 : ℕ) < 1))

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
      (@_root_.D5.S3.Quantum.Codes.MajoranaFourteenModeDistanceFour.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Codes.MajoranaFourteenModeDistanceFour.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Codes.MajoranaFourteenModeDistanceFour.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x < y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Codes.MajoranaFourteenModeDistanceFour
    definition := some {
      owner := `D5.S3.Quantum.Codes.MajoranaFourteenModeDistanceFour
      name := `D5.S3.Quantum.Codes.MajoranaFourteenModeDistanceFour.claim
      path := #[] }
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body",
        "arg", "arg", "fn", "fn"]
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
end Reg.D5.S3.Quantum.Codes.MajoranaFourteenModeDistanceFour
