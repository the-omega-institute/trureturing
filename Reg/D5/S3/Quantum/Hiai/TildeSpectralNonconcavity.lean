import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Hiai.TildeSpectralNonconcavity
import Reg.Support.DependentFamily

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Hiai.TildeSpectralNonconcavity
open LeanInformationAudit
open scoped MatrixOrder Matrix.Norms.L2Operator ComplexOrder

namespace Reg.D5.S3.Quantum.Hiai.TildeSpectralNonconcavity

abbrev signature : Signature where
  Params := Σ _ : ℝ, Σ _ : ℝ, Σ _ : Mat, Σ _ : Mat, Mat
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ z θ =>
    tildeTrace z.1 z.2.1 ((1 - θ) • z.2.2.1 + θ • z.2.2.2.1) z.2.2.2.2)
    (fun e => nomatch e)

noncomputable def rejected : Realization signature :=
  realize signature (fun _ z θ =>
    (1 - θ) * tildeTrace z.1 z.2.1 z.2.2.1 z.2.2.2.2 +
      θ * tildeTrace z.1 z.2.1 z.2.2.2.1 z.2.2.2.2)
    (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α p : ℝ}, 0 < α → α < 1 → α ≠ 1 / 2 → 0 < p →
    ∃ A₀ A₁ B : Mat, A₀.PosDef ∧ A₁.PosDef ∧ B.PosDef ∧
      ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧
        R.readout () ⟨α, p, A₀, A₁, B⟩ θ <
          (1 - θ) * tildeTrace α p A₀ B + θ * tildeTrace α p A₁ B

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨A₀, A₁, B, _, _, _, θ, _, _, bad⟩ :=
    h (α := 1 / 4) (p := 1) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  exact (lt_irrefl _ bad)

noncomputable def family : Registration arena (type_of% (@strict_first_variable_jensen_violation)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@strict_first_variable_jensen_violation, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    obtain ⟨A₀, A₁, B, _, _, _, θ, _, _, hgap⟩ :=
      strict_first_variable_jensen_violation (α := 1 / 4) (p := 1)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    let z : signature.Params := ⟨1 / 4, 1, A₀, A₁, B⟩
    by_cases hzero : actual.readout i z θ = actual.readout i z 0
    · refine ⟨z, θ, 1, ?_⟩
      intro hone
      have h0 : tildeTrace (1 / 4) 1 ((1 - θ) • A₀ + θ • A₁) B =
          tildeTrace (1 / 4) 1 A₀ B := by simpa [actual, realize, z] using hzero
      have h1 : tildeTrace (1 / 4) 1 ((1 - θ) • A₀ + θ • A₁) B =
          tildeTrace (1 / 4) 1 A₁ B := by simpa [actual, realize, z] using hone
      rw [← h0, ← h1] at hgap
      nlinarith
    · exact ⟨z, θ, 0, hzero⟩

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@strict_first_variable_jensen_violation) (Realization signature) Unit Unit := {
  unitName :=
    `D5.S3.Quantum.Hiai.TildeSpectralNonconcavity.strict_first_variable_jensen_violation.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Hiai.TildeSpectralNonconcavity.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature
    (fun _ z θ =>
      tildeTrace z.1 z.2.1 ((1 - θ) • z.2.2.1 + θ • z.2.2.2.1) z.2.2.2.2)
    (fun e => nomatch e))
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Hiai.TildeSpectralNonconcavity
    definition := none
    coordinates := #[0, 1, 6, 7, 8]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "body",
        "arg", "body", "arg", "body", "arg", "arg", "arg", "arg", "body",
        "arg", "arg", "fn", "arg"]
      stateBinder := 9
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration
namespace Classification

abbrev signature : Signature where
  Params := Σ _ : ℝ, Σ _ : ℝ, ℕ
  State z := Matrix (Fin z.2.2) (Fin z.2.2) ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ z := Matrix (Fin z.2.2) (Fin z.2.2) ℂ → ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun _ z A => tildeTrace z.1 z.2.1 A) (fun e => nomatch e)

noncomputable def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => (0 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {α p : ℝ}, 0 < α → α < 1 → 0 < p →
    ((∀ n : ℕ, GeneralizedPerspectiveFunction.JointlyConcaveOn
      {A : Matrix (Fin n) (Fin n) ℂ | A.PosDef} {B : Matrix (Fin n) (Fin n) ℂ | B.PosDef}
      (fun A B => R.readout () ⟨α, p, n⟩ A B)) ↔ α = 1 / 2 ∧ p ≤ 1)

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hc : ∀ n : ℕ, GeneralizedPerspectiveFunction.JointlyConcaveOn
      {A : Matrix (Fin n) (Fin n) ℂ | A.PosDef} {B : Matrix (Fin n) (Fin n) ℂ | B.PosDef}
      (fun A B => rejected.readout () ⟨(1 / 4 : ℝ), (1 : ℝ), n⟩ A B) := by
    intro n A₀ A₁ B₀ B₁ t _ _ _ _ _ _
    simp [rejected, realize]
  have bad := (h (α := 1 / 4) (p := 1) (by norm_num) (by norm_num) (by norm_num)).mp hc
  norm_num at bad

noncomputable def family : Registration arena (type_of% (@joint_concavity_classification)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@joint_concavity_classification, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim j i)).elim
    · intro i
      exact nomatch i
  dependence := by
    intro i
    obtain ⟨A₀, A₁, B, _, _, _, t, _, _, hgap⟩ :=
      strict_first_variable_jensen_violation (α := 1 / 4) (p := 1)
        (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    let z : signature.Params := ⟨1 / 4, 1, 2⟩
    let x : signature.State z := (1 - t) • A₀ + t • A₁
    let x₀ : signature.State z := A₀
    let x₁ : signature.State z := A₁
    by_cases hzero : actual.readout i z x = actual.readout i z x₀
    · refine ⟨z, x, x₁, ?_⟩
      intro hone
      have h0 : tildeTrace (1 / 4) 1 ((1 - t) • A₀ + t • A₁) B =
          tildeTrace (1 / 4) 1 A₀ B := by simpa [actual, realize, z, x, x₀] using congrArg (fun f => f B) hzero
      have h1 : tildeTrace (1 / 4) 1 ((1 - t) • A₀ + t • A₁) B =
          tildeTrace (1 / 4) 1 A₁ B := by simpa [actual, realize, z, x, x₁] using congrArg (fun f => f B) hone
      rw [← h0, ← h1] at hgap
      nlinarith
    · exact ⟨z, x, x₀, hzero⟩

noncomputable def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      (@joint_concavity_classification) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.Hiai.TildeSpectralNonconcavity.joint_concavity_classification.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Hiai.TildeSpectralNonconcavity.Classification.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨True.intro⟩ True.intro
  readout := some (realize signature (fun _ z A => tildeTrace z.1 z.2.1 A) (fun e => nomatch e))
  variation := .evidence ⟨True.intro⟩ True.intro
  sensitivity := .evidence ⟨True.intro⟩ True.intro
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Hiai.TildeSpectralNonconcavity
    definition := none
    coordinates := #[0, 1, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "body", "arg"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
end Classification

end Reg.D5.S3.Quantum.Hiai.TildeSpectralNonconcavity
