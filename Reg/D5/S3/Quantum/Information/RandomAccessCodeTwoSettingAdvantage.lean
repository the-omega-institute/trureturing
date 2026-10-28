import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Information.RandomAccessCodeTwoSettingAdvantage
import Reg.Support.DependentFamily

/-! Source-bound audit of the strict two-setting random access code advantage. -/

namespace Reg.D5.S3.Quantum.Information.RandomAccessCodeTwoSettingAdvantage

open _root_.D5.S3.Quantum.Information.RandomAccessCodeTwoSettingAdvantage
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

/-- Observe success probability as the assignment of measurement settings varies. -/
abbrev signature : Signature where
  Params := Σ n : ℕ, Σ d : ℕ,
    Σ _ : (Fin n → Fin d) → Fin d → ℂ, Fin 2 → Matrix (Fin d) (Fin d) ℂ
  State p := Fin p.1 → Fin 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p s => quantumValue p.1 p.2.1 p.2.2.1 p.2.2.2 s)
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain every dimension bound, normalization, unitary condition and comparison. -/
abbrev arena : Arena where
  signature := signature
  Law r := ∀ n d : ℕ, 2 ≤ n → 2 ≤ d →
    ∃ (ψ : (Fin n → Fin d) → Fin d → ℂ)
      (U : Fin 2 → Matrix (Fin d) (Fin d) ℂ) (s : Fin n → Fin 2),
      (∀ x, star (ψ x) ⬝ᵥ ψ x = 1) ∧
      (∀ i, U i ∈ Matrix.unitaryGroup (Fin d) ℂ) ∧
      ∀ S : ClassicalStrategy n d, classicalValue S < r.readout () ⟨n, d, ψ, U⟩ s

private def classicalWitness : ClassicalStrategy 2 2 where
  Λ := Unit
  finite := inferInstance
  weight _ := 1
  nonneg _ := zero_le_one
  total := by simp
  encode _ _ := 0
  decode _ _ _ := 0

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨ψ, U, s, _, _, hbound⟩ := h 2 2 (by norm_num) (by norm_num)
  have hbad := hbound classicalWitness
  change classicalValue classicalWitness < 0 at hbad
  have hnonneg : 0 ≤ classicalValue classicalWitness := by
    unfold classicalValue deterministicValue
    apply Finset.sum_nonneg
    intro l _
    apply mul_nonneg (classicalWitness.nonneg l)
    apply mul_nonneg (by positivity)
    apply Finset.sum_nonneg
    intro x _
    apply Finset.sum_nonneg
    intro j _
    split_ifs <;> norm_num
  exact (not_lt_of_ge hnonneg) hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨2, 2, (fun _ _ => 1), (fun t _ _ => if t = 0 then 0 else 1)⟩,
    (fun _ => 0), (fun _ => 1), ?_⟩
  change quantumValue 2 2 (fun _ _ => 1) (fun t _ _ => if t = 0 then 0 else 1)
      (fun _ => 0) ≠
    quantumValue 2 2 (fun _ _ => 1) (fun t _ _ => if t = 0 then 0 else 1) (fun _ => 1)
  norm_num [quantumValue, dotProduct, Fin.sum_univ_two]

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
      (@_root_.D5.S3.Quantum.Information.RandomAccessCodeTwoSettingAdvantage.result)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Information.RandomAccessCodeTwoSettingAdvantage.unit
  realizationName :=
    `Reg.D5.S3.Quantum.Information.RandomAccessCodeTwoSettingAdvantage.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some
    (realize signature (fun _ p s => quantumValue p.1 p.2.1 p.2.2.1 p.2.2.2 s)
      (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Information.RandomAccessCodeTwoSettingAdvantage
    definition := some {
      owner := `D5.S3.Quantum.Information.RandomAccessCodeTwoSettingAdvantage
      name := `D5.S3.Quantum.Information.RandomAccessCodeTwoSettingAdvantage.claim
      path := #[] }
    coordinates := #[0, 1, 4, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "body",
        "arg", "body", "arg", "arg", "body", "arg"]
      stateBinder := 6
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end
end Reg.D5.S3.Quantum.Information.RandomAccessCodeTwoSettingAdvantage
