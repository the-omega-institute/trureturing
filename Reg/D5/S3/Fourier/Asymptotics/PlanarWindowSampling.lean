import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.Asymptotics.PlanarWindowSampling
import Reg.Support.SingleDependentReadout

/-! Source-bound registration of the sampling-error budget. -/

namespace Reg.D5.S3.Fourier.Asymptotics.PlanarWindowSampling

open _root_.D5.S3.Fourier.Asymptotics.PlanarWindowSampling
open _root_.D5.S3.Fourier.Asymptotics.PlanarFourierTail
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory WithLp
open scoped BigOperators ContDiff

noncomputable section

universe u

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, Σ _ : ℝ, Σ _ : ℕ, ℝ)
    (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ b d =>
    27 * b.1 * b.2.2.2 + (27 * b.1 / b.2.1 ^ 2) * d +
      2 * b.1 / (b.2.1 ^ 4 * (b.2.2.1 : ℝ) ^ 4)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {ι : Type u} (f : Plane → ℂ), HasCompactSupport f → ContDiff ℝ ∞ f →
    ∃ K ≥ (0 : ℝ), ∀ (ε : ℝ), 0 < ε → ε ≤ 1 →
      ∀ (center : Plane) (s : Finset ι) (w : ι → ℝ) (p : ι → Plane)
        (J : ℕ) (c d : ℝ), 0 ≤ c → 0 ≤ d → 0 < J →
        (∀ i ∈ s, 0 ≤ w i) → (∑ i ∈ s, w i = 1) →
        (∀ m ≠ (0, 0), modeRadius m ≤ J →
          ‖∑ i ∈ s, (w i : ℂ) * character m (p i)‖ ≤ c + d * (modeRadius m : ℝ) ^ 2) →
        ‖(∑ i ∈ s, (w i : ℂ) *
          ∑' a : Fin 2 → ℤ, f (ε⁻¹ • (toLp 2 (fun j => (a j : ℝ)) + p i - center))) -
          (ε ^ 2 : ℝ) • (∫ x, f x)‖ ≤ R.readout () ⟨K, ε, J, c⟩ d

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hs : HasCompactSupport (0 : Plane → ℂ) := by
    change IsCompact (tsupport (0 : Plane → ℂ))
    simp
  obtain ⟨K, _, bound⟩ := h (ι := PUnit.{u + 1}) (fun _ => 0) hs contDiff_const
  have hmode (m : ℤ × ℤ) : ‖character m (0 : Plane)‖ ≤ 1 := (Circle.norm_coe _).le
  have hbad := bound 1 zero_lt_one le_rfl 0 {PUnit.unit} (fun _ => 1) (fun _ => 0)
    1 1 0 zero_le_one le_rfl Nat.one_pos (by simp) (by simp)
    (fun m _ _ => by simpa using hmode m)
  norm_num [rejected, realize] at hbad

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨1, 1, 1, 0⟩, 0, 1, ?_⟩
  norm_num [actual, realize]

def source_registration : Registration arena.{u} (type_of% @compact_window_sampling.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨compact_window_sampling, rejected, rejected_law⟩
  sensitivity :=
    Reg.Support.SingleDependentReadout.sensitivity arena.{u}.Law actual rejected rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@compact_window_sampling.{u}) (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Fourier.Asymptotics.PlanarWindowSampling.unit
  realizationName := `Reg.D5.S3.Fourier.Asymptotics.PlanarWindowSampling.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ b d =>
    27 * b.1 * b.2.2.2 + (27 * b.1 / b.2.1 ^ 2) * d +
      2 * b.1 / (b.2.1 ^ 4 * (b.2.2.1 : ℝ) ^ 4)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.Asymptotics.PlanarWindowSampling
    definition := none
    coordinates := #[4, 5, 12, 13]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 14
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration

end

end Reg.D5.S3.Fourier.Asymptotics.PlanarWindowSampling
