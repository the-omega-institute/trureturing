import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.QuaternionReadingOnePointExtension
import Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive
import Reg.Support.SingleDependentReadout

/-! Source-bound audits of the one-point extensions of the unit-quaternion reading.

For the two classifications the readout is the affine reading `(a + ⟪b, x⟫) / √2` of the new
point, as a function of the old point `x` with the coefficients `a` and `b` as coordinates; the
extension function, the self-reading and every condition on `a` and `b` stay in the law
verbatim. For the equality cases the readout is the reading `kappa x x₀` of an old point. All
rejected laws use the constant reading `1 / √2`, the affine reading with `a = 1` and `b = 0`: it
has nonnegative extended Gram forms with self-reading one, has feature rank five, is
nonnegative, and never vanishes. -/

namespace Reg.D5.S3.Quantum.AURICOmega.QuaternionReadingOnePointExtension

open _root_.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open _root_.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open _root_.D5.S3.Quantum.AURICOmega.QuaternionReadingOnePointExtension
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive (one_ne_neg_one)
open LeanInformationAudit

open scoped InnerProductSpace Quaternion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section

/-- The affine reading with `a = 1` and `b = 0`, the constant `1 / √2`. -/
def constReading : unitary ℍ[ℝ] → ℝ := fun x => (1 + ⟪(0 : ℍ[ℝ]), (x : ℍ[ℝ])⟫_ℝ) / Real.sqrt 2

theorem constReading_ne_zero (x : unitary ℍ[ℝ]) : constReading x ≠ 0 := by
  have h : 0 < Real.sqrt 2 := by positivity
  simp only [constReading, inner_zero_left, add_zero]
  exact (one_div_pos.mpr h).ne'

/-! The affine reading `(a + ⟪b, x⟫) / √2` in the two classifications. -/
namespace Affine

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℝ, ℍ[ℝ]) (fun _ => unitary ℍ[ℝ]) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p s => (p.1 + ⟪p.2, (s : ℍ[ℝ])⟫_ℝ) / Real.sqrt 2) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨⟨0, 1⟩, 1, -1, ?_⟩
  change ((0 : ℝ) + ⟪(1 : ℍ[ℝ]), ((1 : unitary ℍ[ℝ]) : ℍ[ℝ])⟫_ℝ) / Real.sqrt 2 ≠
    ((0 : ℝ) + ⟪(1 : ℍ[ℝ]), ((-1 : unitary ℍ[ℝ]) : ℍ[ℝ])⟫_ℝ) / Real.sqrt 2
  have h1 : ⟪(1 : ℍ[ℝ]), (1 : ℍ[ℝ])⟫_ℝ = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_one, one_pow]
  have hσ : 0 < Real.sqrt 2 := by positivity
  rw [Unitary.coe_neg, OneMemClass.coe_one, inner_neg_right, h1]
  intro h
  rw [div_left_inj' hσ.ne'] at h
  norm_num at h

/-- Retain the complete telescope and both sides of `onePointExtension_iff`; only the affine
reading on the right is read out. -/
abbrev extensionArena : Arena where
  signature := signature
  Law rd := ∀ (f : unitary ℍ[ℝ] → ℝ) (d : ℝ),
    (∀ (n : ℕ) (x : Fin n → unitary ℍ[ℝ]) (c : Fin n → ℝ) (t : ℝ),
        0 ≤ d * t ^ 2 + 2 * t * ∑ i, c i * f (x i) +
          ∑ i, ∑ j, c i * c j * quaternionModel.kappa (x i) (x j)) ↔
      ∃ (a : ℝ) (b : ℍ[ℝ]), a ^ 2 + ‖b‖ ^ 2 ≤ d ∧
        ∀ x : unitary ℍ[ℝ], f x = rd.readout () ⟨a, b⟩ x

theorem extension_rejected_law : ¬ extensionArena.Law rejected := by
  intro h
  obtain ⟨a, b, -, hx⟩ := (h constReading 1).mp
    ((onePointExtension_iff constReading 1).mpr ⟨1, 0, by simp, fun _ => rfl⟩)
  exact constReading_ne_zero 1 (hx 1)

/-- The exact statement of `onePointExtension_iff`. -/
abbrev extensionStatement : Prop := type_of% @onePointExtension_iff

def extension_registration : Registration extensionArena extensionStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@onePointExtension_iff, rejected, extension_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity extensionArena.Law
    actual rejected extension_rejected_law
  dependence := dependence

/-- Retain the complete telescope and both sides of `hasOnePointFeatureRank_five_iff`; only the
affine reading on the right is read out. -/
abbrev rankFiveArena : Arena where
  signature := signature
  Law rd := ∀ (f : unitary ℍ[ℝ] → ℝ),
    (HasOnePointFeatureRank f 5 ∧ ∀ x, 0 ≤ f x) ↔
      ∃ (a : ℝ) (b : ℍ[ℝ]), ‖b‖ ≤ a ∧ a ^ 2 + ‖b‖ ^ 2 = 1 ∧
        ∀ x : unitary ℍ[ℝ], f x = rd.readout () ⟨a, b⟩ x

theorem rankFive_rejected_law : ¬ rankFiveArena.Law rejected := by
  intro h
  obtain ⟨a, b, -, -, hx⟩ := (h constReading).mp
    ((hasOnePointFeatureRank_five_iff constReading).mpr ⟨1, 0, by simp, by simp, fun _ => rfl⟩)
  exact constReading_ne_zero 1 (hx 1)

/-- The exact statement of `hasOnePointFeatureRank_five_iff`. -/
abbrev rankFiveStatement : Prop := type_of% @hasOnePointFeatureRank_five_iff

def rankFive_registration : Registration rankFiveArena rankFiveStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@hasOnePointFeatureRank_five_iff, rejected, rankFive_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity rankFiveArena.Law
    actual rejected rankFive_rejected_law
  dependence := dependence

end Affine

/-! The reading `kappa x x₀` of an old point in the equality cases. -/
namespace Point

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (unitary ℍ[ℝ]) (fun _ => unitary ℍ[ℝ]) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ p s => quaternionModel.kappa s p) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1 / Real.sqrt 2) (fun e => nomatch e)

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 1, -1, fun e => ?_⟩
  change quaternionModel.kappa 1 1 = quaternionModel.kappa (-1) 1 at e
  rw [quaternionModel.kappa_self] at e
  exact one_ne_neg_one ((quaternionModel.kappa_eq_one_iff (-1) 1).1 e.symm).symm

/-- Retain the complete telescope and all three entries of
`tfae_eq_kappa_of_hasOnePointFeatureRank_five`; only the reading of the old point in the third
entry is read out. -/
abbrev arena : Arena where
  signature := signature
  Law rd := ∀ (f : unitary ℍ[ℝ] → ℝ), HasOnePointFeatureRank f 5 → (∀ x, 0 ≤ f x) →
    List.TFAE [∃ x₁, f x₁ = 0, ∃ x₁, f x₁ = 1, ∃ x₀, ∀ x, f x = rd.readout () x₀ x]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨hf, h0⟩ :=
    (hasOnePointFeatureRank_five_iff constReading).mpr ⟨1, 0, by simp, by simp, fun _ => rfl⟩
  have h3 : ∃ x₀, ∀ x, constReading x = rejected.readout () x₀ x := ⟨1, fun x => by
    change constReading x = 1 / Real.sqrt 2
    simp only [constReading, inner_zero_left, add_zero]⟩
  obtain ⟨x₁, hx₁⟩ := ((h constReading hf h0).out 3 1).mp h3
  exact constReading_ne_zero x₁ hx₁

/-- The exact statement of `tfae_eq_kappa_of_hasOnePointFeatureRank_five`. -/
abbrev sourceStatement : Prop := type_of% @tfae_eq_kappa_of_hasOnePointFeatureRank_five

def source_registration : Registration arena sourceStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@tfae_eq_kappa_of_hasOnePointFeatureRank_five, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law
    actual rejected rejected_law
  dependence := dependence

end Point

def onePointExtension_iff_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@onePointExtension_iff) (Realization Affine.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionReadingOnePointExtension.onePointExtension_iff_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionReadingOnePointExtension.Affine.extension_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Affine.extensionArena⟩
  objectArena := .source ⟨Affine.extensionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Affine.extensionArena ⟨Affine.extension_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Affine.signature
    (fun _ p s => (p.1 + ⟪p.2, (s : ℍ[ℝ])⟫_ℝ) / Real.sqrt 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionReadingOnePointExtension
    definition := none
    coordinates := #[2, 3]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "body", "arg", "body", "arg", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def hasOnePointFeatureRank_five_iff_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@hasOnePointFeatureRank_five_iff) (Realization Affine.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionReadingOnePointExtension.hasOnePointFeatureRank_five_iff_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionReadingOnePointExtension.Affine.rankFive_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Affine.rankFiveArena⟩
  objectArena := .source ⟨Affine.rankFiveArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Affine.rankFiveArena ⟨Affine.rankFive_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Affine.signature
    (fun _ p s => (p.1 + ⟪p.2, (s : ℍ[ℝ])⟫_ℝ) / Real.sqrt 2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionReadingOnePointExtension
    definition := none
    coordinates := #[1, 2]
    readouts := #[{
      path := #["body", "arg", "arg", "body", "arg", "body", "arg", "arg", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def tfae_eq_kappa_of_hasOnePointFeatureRank_five_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@tfae_eq_kappa_of_hasOnePointFeatureRank_five) (Realization Point.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionReadingOnePointExtension.tfae_eq_kappa_of_hasOnePointFeatureRank_five_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionReadingOnePointExtension.Point.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Point.arena⟩
  objectArena := .source ⟨Point.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Point.arena ⟨Point.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Point.signature
    (fun _ p s => quaternionModel.kappa s p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionReadingOnePointExtension
    definition := none
    coordinates := #[3]
    readouts := #[{
      path := #["body", "body", "body", "arg", "arg", "arg", "fn", "arg", "arg", "body", "body",
        "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.AURICOmega.QuaternionReadingOnePointExtension
