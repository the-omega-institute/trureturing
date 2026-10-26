import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Codes.CssTDoublingMapImprovement
import Reg.Support.DependentFamily

/-! Source-bound audit of the strict CSS-T doubling-map improvement. -/

namespace Reg.D5.S3.Quantum.Codes.CssTDoublingMapImprovement

open _root_.D5.S3.Quantum.Codes.CssTDoublingMapImprovement
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Module

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe the distance with the lower extension code as the state. -/
abbrev signature : Signature where
  Params := Σ n : ℕ, Σ C₁ : Submodule (ZMod 2) (Fin n → ZMod 2),
    C₁ →ₗ[ZMod 2] (Fin n → ZMod 2)
  State p := Submodule (ZMod 2) (Fin p.1 ⊕ Fin p.1 → ZMod 2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature
    (fun _ p C => cssDistance C (extension (le_refl p.2.1) p.2.2))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the code inclusion, rank gap, admissibility, and strict distance gain. -/
abbrev arena : Arena where
  signature := signature
  Law R :=
    ∃ (n : ℕ) (C₂ C₁ : Submodule (ZMod 2) (Fin n → ZMod 2)) (h : C₂ ≤ C₁),
      finrank (ZMod 2) C₂ < finrank (ZMod 2) C₁ ∧
        ∃ φ : C₁ →ₗ[ZMod 2] (Fin n → ZMod 2), admissible C₂ C₁ h φ ∧
          R.readout () ⟨n, C₁, φ⟩ (extension h φ) >
            cssDistance (extension h C₁.subtype) (extension (le_refl C₁) C₁.subtype)

theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨n, C₂, C₁, h, _, φ, _, hbad⟩
  change 0 > cssDistance (extension h C₁.subtype)
    (extension (le_refl C₁) C₁.subtype) at hbad
  exact (Nat.not_lt_zero _) hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨n, C₂, C₁, h, _, φ, _, hgain⟩ := result
  refine ⟨⟨n, C₁, φ⟩, extension h φ, extension (le_refl C₁) φ, ?_⟩
  change cssDistance (extension h φ) (extension (le_refl C₁) φ) ≠
    cssDistance (extension (le_refl C₁) φ) (extension (le_refl C₁) φ)
  have hz : cssDistance (extension (le_refl C₁) φ) (extension (le_refl C₁) φ) = 0 := by
    have hempty (C : Submodule (ZMod 2) (Fin n ⊕ Fin n → ZMod 2)) :
        {d : ℕ | ∃ x, x ∈ C ∧ x ∉ C ∧ hammingNorm x = d} = ∅ := by
      ext d
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨x, hx, hn, _⟩
      exact hn hx
    unfold cssDistance
    rw [hempty, hempty, Set.union_self]
    exact Nat.sInf_empty
  rw [hz]
  exact Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hgain)

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
      (@_root_.D5.S3.Quantum.Codes.CssTDoublingMapImprovement.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Codes.CssTDoublingMapImprovement.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Codes.CssTDoublingMapImprovement.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p C => cssDistance C (extension (le_refl p.2.1) p.2.2))
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Codes.CssTDoublingMapImprovement
    definition := some {
      owner := `D5.S3.Quantum.Codes.CssTDoublingMapImprovement
      name := `D5.S3.Quantum.Codes.CssTDoublingMapImprovement.claim
      path := #[] }
    coordinates := #[0, 2, 4]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "arg", "body", "arg", "body",
        "arg", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Codes.CssTDoublingMapImprovement
