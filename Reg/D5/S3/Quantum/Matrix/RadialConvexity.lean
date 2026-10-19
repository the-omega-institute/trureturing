import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Matrix.RadialConvexity
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Quantum.Matrix.RadialConvexity
open _root_.D5.S3.Quantum.Matrix.RadialConvexity
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Set
open scoped RealInnerProductSpace
noncomputable section

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ t => t) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

def theoremLaw (R : Realization signature) : Prop :=
  ∀ {E F : Type}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [PartialOrder E] [IsOrderedAddMonoid E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (s : Set E) (g : E → F) (D : E → E →L[ℝ] F),
    (∀ U ∈ s, ∀ V ∈ s, U ≤ V → ∀ t : ℝ, R.readout () () t ∈ Icc (0 : ℝ) 1 →
      U + t • (V - U) ∈ s ∧ U ≤ U + t • (V - U) ∧ U + t • (V - U) ≤ V) →
    (∀ C ∈ s, HasFDerivAt g (D C) C) →
    EndpointDerivativePositive s g D →
    ∀ {A C B : E}, A ∈ s → C ∈ s → B ∈ s → A ≤ C → C ≤ B →
      ‖g C - g A‖ ≤ ‖g B - g A‖ ∧ ‖g B - g C‖ ≤ ‖g B - g A‖
abbrev arena : Arena where
  signature := signature
  Law := theoremLaw
abbrev sourceScope := type_of% (@radial_inequalities_of_endpoint_derivative)

private theorem bridge : sourceScope ↔ arena.Law actual := Iff.rfl

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let s : Set ℝ := {x | x = -1 ∨ x = 0 ∨ x = 1}
  let g : ℝ → ℝ := fun x => (x ^ 2 - 1) ^ 2
  let D : ℝ → ℝ →L[ℝ] ℝ := 0
  have hs : ∀ U ∈ s, ∀ V ∈ s, U ≤ V → ∀ t : ℝ,
      rejected.readout () () t ∈ Icc (0 : ℝ) 1 →
      U + t * (V - U) ∈ s ∧ U ≤ U + t * (V - U) ∧ U + t * (V - U) ≤ V := by
    intro U hU V hV hUV t ht
    have hh : (2 : ℝ) ≤ 1 := ht.2
    norm_num at hh
  have hg (x : ℝ) : HasDerivAt g (2 * (x ^ 2 - 1) * (2 * x)) x := by
    convert (((hasDerivAt_id x).pow 2).sub_const 1).pow 2 using 1
    · ext y
      simp [g, Pi.pow_apply]
    · simp [Pi.pow_apply]
      <;> ring
  have hd : ∀ x ∈ s, HasFDerivAt g (D x) x := by
    intro x hx
    rcases hx with rfl | rfl | rfl
    · simpa [D] using (hg (-1)).hasFDerivAt
    · simpa [D] using (hg 0).hasFDerivAt
    · simpa [D] using (hg 1).hasFDerivAt
  have hp : EndpointDerivativePositive s g D := by
    intro U hU V hV hUV K hK
    simp [D]
  have hh := h s g D hs hd hp (A := -1) (C := 0) (B := 1)
    (by exact Or.inl rfl) (by exact Or.inr (Or.inl rfl))
    (by exact Or.inr (Or.inr rfl)) (by norm_num) (by norm_num)
  norm_num [g] at hh

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨(), 0, 1, by norm_num [actual, realize]⟩

def source_registration : Registration arena sourceScope where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@radial_inequalities_of_endpoint_derivative), rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@radial_inequalities_of_endpoint_derivative) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Matrix.RadialConvexity.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.RadialConvexity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ t => t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.RadialConvexity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "domain", "body", "body", "body", "body", "body",
        "body", "domain", "arg"]
      stateBinder := 16
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end
end Reg.D5.S3.Quantum.Matrix.RadialConvexity
