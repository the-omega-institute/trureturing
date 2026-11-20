import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.QuaternionReadingOnePointExtension
import Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive
import Reg.Support.SingleDependentReadout

/-! Source-bound audits of the one-point extensions of the unit-quaternion reading.

For the nonnegativity criterion and the two classifications the readout is the affine reading
`(a + ⟪b, x⟫) / √2`, as a function of the unit quaternion `x` with the coefficients `a` and `b`
as coordinates; everything else stays in the law verbatim. For the two characterizations of the
readings of old points the readout is the reading `kappa x x₀` of an old point. The rejected
readouts are the constants `0` and `1 / √2`. They are refuted by the affine reading with `a = 1`
and `b = 0`, the constant `1 / √2`: it has nonnegative extended Gram forms with self-reading one,
has feature rank five, is nonnegative, and never takes the value zero or one; and, for the
nonnegativity criterion, by `a = -1` and `b = 0`. -/

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

theorem constReading_eq (x : unitary ℍ[ℝ]) : constReading x = 1 / Real.sqrt 2 := by
  simp only [constReading, inner_zero_left, add_zero]

theorem constReading_ne_one (x : unitary ℍ[ℝ]) : constReading x ≠ 1 := by
  have hσ : 0 < Real.sqrt 2 := by positivity
  rw [constReading_eq]
  intro h
  rw [div_eq_one_iff_eq hσ.ne'] at h
  have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [← h] at h2
  norm_num at h2

/-! The affine reading `(a + ⟪b, x⟫) / √2` in the nonnegativity criterion and the two
classifications. -/
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

/-- Retain the complete telescope and both sides of `forall_nonneg_iff_norm_le`; only the affine
reading on the left is read out. -/
abbrev nonnegArena : Arena where
  signature := signature
  Law rd := ∀ (a : ℝ) (b : ℍ[ℝ]),
    (∀ x : unitary ℍ[ℝ], 0 ≤ rd.readout () ⟨a, b⟩ x) ↔ ‖b‖ ≤ a

theorem nonneg_rejected_law : ¬ nonnegArena.Law rejected := by
  intro h
  have h1 := (h (-1) 0).mp fun _ => le_refl (0 : ℝ)
  rw [norm_zero] at h1
  norm_num at h1

/-- The exact statement of `forall_nonneg_iff_norm_le`. -/
abbrev nonnegStatement : Prop := type_of% @forall_nonneg_iff_norm_le

def nonneg_registration : Registration nonnegArena nonnegStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@forall_nonneg_iff_norm_le, rejected, nonneg_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity nonnegArena.Law
    actual rejected nonneg_rejected_law
  dependence := dependence

/-- Retain the complete telescope and all three entries of `tfae_onePointExtension`; only the
affine reading in the third entry is read out. -/
abbrev extensionArena : Arena where
  signature := signature
  Law rd := ∀ (f : unitary ℍ[ℝ] → ℝ) (d : ℝ),
    List.TFAE [∀ (n : ℕ) (x : Fin n → unitary ℍ[ℝ]) (c : Fin n → ℝ) (t : ℝ),
        0 ≤ d * t ^ 2 + 2 * t * ∑ i, c i * f (x i) +
          ∑ i, ∑ j, c i * c j * quaternionModel.kappa (x i) (x j),
      ∀ (x : Fin 6 → unitary ℍ[ℝ]) (c : Fin 6 → ℝ) (t : ℝ),
        0 ≤ d * t ^ 2 + 2 * t * ∑ i, c i * f (x i) +
          ∑ i, ∑ j, c i * c j * quaternionModel.kappa (x i) (x j),
      ∃ (a : ℝ) (b : ℍ[ℝ]), a ^ 2 + ‖b‖ ^ 2 ≤ d ∧
        ∀ x : unitary ℍ[ℝ], f x = rd.readout () ⟨a, b⟩ x]

theorem extension_rejected_law : ¬ extensionArena.Law rejected := by
  intro h
  have h3 : ∃ (a : ℝ) (b : ℍ[ℝ]), a ^ 2 + ‖b‖ ^ 2 ≤ 1 ∧
      ∀ x : unitary ℍ[ℝ], constReading x = (a + ⟪b, (x : ℍ[ℝ])⟫_ℝ) / Real.sqrt 2 :=
    ⟨1, 0, by simp, fun _ => rfl⟩
  have hpsd := ((tfae_onePointExtension constReading 1).out 3 1).mp h3
  obtain ⟨a, b, -, hx⟩ := ((h constReading 1).out 1 3).mp hpsd
  exact constReading_ne_zero 1 (hx 1)

/-- The exact statement of `tfae_onePointExtension`. -/
abbrev extensionStatement : Prop := type_of% @tfae_onePointExtension

def extension_registration : Registration extensionArena extensionStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@tfae_onePointExtension, rejected, extension_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity extensionArena.Law
    actual rejected extension_rejected_law
  dependence := dependence

/-- Retain the complete telescope and both sides of `hasOnePointFeatureRank_five_iff`; only the
affine reading on the right is read out. -/
abbrev rankFiveArena : Arena where
  signature := signature
  Law rd := ∀ (f : unitary ℍ[ℝ] → ℝ),
    HasOnePointFeatureRank f 5 ↔ ∃ (a : ℝ) (b : ℍ[ℝ]), a ^ 2 + ‖b‖ ^ 2 = 1 ∧
      ∀ x : unitary ℍ[ℝ], f x = rd.readout () ⟨a, b⟩ x

theorem rankFive_rejected_law : ¬ rankFiveArena.Law rejected := by
  intro h
  obtain ⟨a, b, -, hx⟩ := (h constReading).mp
    ((hasOnePointFeatureRank_five_iff constReading).mpr ⟨1, 0, by simp, fun _ => rfl⟩)
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

/-- Retain the complete telescope and both sides of `exists_eq_one_iff_exists_eq_kappa`; only the
reading of the old point on the right is read out. -/
abbrev oneArena : Arena where
  signature := signature
  Law rd := ∀ (f : unitary ℍ[ℝ] → ℝ),
    (∀ (n : ℕ) (x : Fin n → unitary ℍ[ℝ]) (c : Fin n → ℝ) (t : ℝ),
      0 ≤ t ^ 2 + 2 * t * ∑ i, c i * f (x i) +
        ∑ i, ∑ j, c i * c j * quaternionModel.kappa (x i) (x j)) →
    ((∃ x₁, f x₁ = 1) ↔ ∃ x₀, ∀ x, f x = rd.readout () x₀ x)

theorem one_rejected_law : ¬ oneArena.Law rejected := by
  intro h
  have h3 : ∃ (a : ℝ) (b : ℍ[ℝ]), a ^ 2 + ‖b‖ ^ 2 ≤ 1 ∧
      ∀ x : unitary ℍ[ℝ], constReading x = (a + ⟪b, (x : ℍ[ℝ])⟫_ℝ) / Real.sqrt 2 :=
    ⟨1, 0, by simp, fun _ => rfl⟩
  have hpsd := ((tfae_onePointExtension constReading 1).out 3 1).mp h3
  have hf : ∀ (n : ℕ) (x : Fin n → unitary ℍ[ℝ]) (c : Fin n → ℝ) (t : ℝ),
      0 ≤ t ^ 2 + 2 * t * ∑ i, c i * constReading (x i) +
        ∑ i, ∑ j, c i * c j * quaternionModel.kappa (x i) (x j) := fun n x c t => by
    simpa only [one_mul] using hpsd n x c t
  have hr : ∃ x₀, ∀ x, constReading x = rejected.readout () x₀ x := ⟨1, fun x => constReading_eq x⟩
  obtain ⟨x₁, hx₁⟩ := (h constReading hf).mpr hr
  exact constReading_ne_one x₁ hx₁

/-- The exact statement of `exists_eq_one_iff_exists_eq_kappa`. -/
abbrev oneStatement : Prop := type_of% @exists_eq_one_iff_exists_eq_kappa

def one_registration : Registration oneArena oneStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_eq_one_iff_exists_eq_kappa, rejected, one_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity oneArena.Law
    actual rejected one_rejected_law
  dependence := dependence

/-- Retain the complete telescope and both sides of `exists_eq_zero_iff_exists_eq_kappa`; only
the reading of the old point on the right is read out. -/
abbrev zeroArena : Arena where
  signature := signature
  Law rd := ∀ (f : unitary ℍ[ℝ] → ℝ), HasOnePointFeatureRank f 5 → (∀ x, 0 ≤ f x) →
    ((∃ x₁, f x₁ = 0) ↔ ∃ x₀, ∀ x, f x = rd.readout () x₀ x)

theorem zero_rejected_law : ¬ zeroArena.Law rejected := by
  intro h
  have hf := (hasOnePointFeatureRank_five_iff constReading).mpr ⟨1, 0, by simp, fun _ => rfl⟩
  have h0 : ∀ x, 0 ≤ constReading x := (forall_nonneg_iff_norm_le 1 0).mpr (by simp)
  have hr : ∃ x₀, ∀ x, constReading x = rejected.readout () x₀ x := ⟨1, fun x => constReading_eq x⟩
  obtain ⟨x₁, hx₁⟩ := (h constReading hf h0).mpr hr
  exact constReading_ne_zero x₁ hx₁

/-- The exact statement of `exists_eq_zero_iff_exists_eq_kappa`. -/
abbrev zeroStatement : Prop := type_of% @exists_eq_zero_iff_exists_eq_kappa

def zero_registration : Registration zeroArena zeroStatement where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_eq_zero_iff_exists_eq_kappa, rejected, zero_rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity zeroArena.Law
    actual rejected zero_rejected_law
  dependence := dependence

end Point

def forall_nonneg_iff_norm_le_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@forall_nonneg_iff_norm_le) (Realization Affine.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionReadingOnePointExtension.forall_nonneg_iff_norm_le_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionReadingOnePointExtension.Affine.nonneg_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Affine.nonnegArena⟩
  objectArena := .source ⟨Affine.nonnegArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Affine.nonnegArena ⟨Affine.nonneg_registration⟩
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
    coordinates := #[0, 1]
    readouts := #[{
      path := #["fn", "arg", "body", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def tfae_onePointExtension_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@tfae_onePointExtension) (Realization Affine.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionReadingOnePointExtension.tfae_onePointExtension_unit
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
      path := #["body", "body", "arg", "arg", "arg", "fn", "arg", "arg", "body", "arg", "body", "arg", "body", "arg"]
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
      path := #["body", "arg", "arg", "body", "arg", "body", "arg", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def exists_eq_one_iff_exists_eq_kappa_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_eq_one_iff_exists_eq_kappa) (Realization Point.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionReadingOnePointExtension.exists_eq_one_iff_exists_eq_kappa_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionReadingOnePointExtension.Point.one_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Point.oneArena⟩
  objectArena := .source ⟨Point.oneArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Point.oneArena ⟨Point.one_registration⟩
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
    coordinates := #[2]
    readouts := #[{
      path := #["body", "body", "arg", "arg", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def exists_eq_zero_iff_exists_eq_kappa_registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_eq_zero_iff_exists_eq_kappa) (Realization Point.signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionReadingOnePointExtension.exists_eq_zero_iff_exists_eq_kappa_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionReadingOnePointExtension.Point.zero_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Point.zeroArena⟩
  objectArena := .source ⟨Point.zeroArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Point.zeroArena ⟨Point.zero_registration⟩
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
      path := #["body", "body", "body", "arg", "arg", "body", "body", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.Quantum.AURICOmega.QuaternionReadingOnePointExtension
