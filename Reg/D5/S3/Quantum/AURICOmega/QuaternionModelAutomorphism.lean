import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.AURICOmega.QuaternionModelAutomorphism
import Reg.D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity
import Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive
import Reg.Support.DependentFamily

/-! Source-bound audits of the rigidity of the unit quaternion comparison model and of the
two-to-one parametrization of left-right translations.

Both registrations read the left-right translation `p * s * q` by the two existential or
universal unit quaternions, with the signature, readouts and observational dependence of the
translation audit of `QuaternionTwoPointHomogeneity`. The rejected readout is the identity. For
the rigidity theorem it is refuted on the unit quaternion comparison model lifted to an arbitrary
universe, with `u = ULift.down` and `v x = -1 * x.down * 1`, which preserves the transfer and the
reading but is not `u`. -/

namespace Reg.D5.S3.Quantum.AURICOmega.QuaternionModelAutomorphism

open _root_.D5.S3.Quantum.AURICOmega.TernaryComparisonGroup
open _root_.D5.S3.Quantum.AURICOmega.QuaternionComparisonModel
open _root_.D5.S3.Quantum.AURICOmega.QuaternionModelAutomorphism
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.Reg.D5.S3.Quantum.AURICOmega.TernaryComparisonRankFive (liftedModel one_ne_neg_one)

open scoped Quaternion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.longLine false
noncomputable section
universe u

/-! The translation `p * u x * q` on the right of `preserves_iff_exists_mul_mul`. -/
namespace Rigidity

/-- Retain the complete carrier, structure, map, hypothesis and second-map telescope and both
sides of the equivalence of `preserves_iff_exists_mul_mul`. -/
abbrev arena : Arena where
  signature := Reg.D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity.Translation.signature
  Law r := ∀ {M : Type u} (C : TernaryComparison M) (u : M → unitary ℍ[ℝ]),
    (∀ x y z : M, u (C.tri x y z) = quaternionModel.tri (u x) (u y) (u z)) →
    (∀ x y : M, quaternionModel.kappa (u x) (u y) = C.kappa x y) →
    ∀ v : M → unitary ℍ[ℝ],
      ((∀ x y z : M, v (C.tri x y z) = quaternionModel.tri (v x) (v y) (v z)) ∧
          ∀ x y : M, quaternionModel.kappa (v x) (v y) = C.kappa x y) ↔
        ∃ p q : unitary ℍ[ℝ], ∀ x : M, v x = r.readout () ⟨p, q⟩ (u x)

/-- The identity readout would force `v = u` for every transfer- and reading-preserving `v`. -/
theorem rejected_law :
    ¬ arena.{u}.Law Reg.D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity.Translation.rejected := by
  intro h
  have hv := (preserves_iff_exists_mul_mul liftedModel.{u} ULift.down (fun _ _ _ => rfl)
    (fun _ _ => rfl) (fun x => -1 * x.down * 1)).mpr ⟨-1, 1, fun _ => rfl⟩
  obtain ⟨p, q, hpq⟩ := (h liftedModel.{u} ULift.down (fun _ _ _ => rfl) (fun _ _ => rfl)
    (fun x => -1 * x.down * 1)).mp hv
  have h1 : (-1 : unitary ℍ[ℝ]) * 1 * 1 = 1 := hpq ⟨1⟩
  rw [mul_one, mul_one] at h1
  exact one_ne_neg_one h1.symm

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @preserves_iff_exists_mul_mul.{u}

def source_registration : Registration arena.{u} sourceStatement.{u} where
  actual := Reg.D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity.Translation.actual
  bridge := Iff.rfl
  variation := ⟨@preserves_iff_exists_mul_mul.{u},
    Reg.D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity.Translation.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨Reg.D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity.Translation.rejected,
        fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := Reg.D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity.Translation.dependence

end Rigidity

/-! The translation `p * x * q` on the left of `mul_mul_eq_mul_mul_iff`. -/
namespace Parametrization

/-- Retain the complete argument telescope and both sides of the equivalence of
`mul_mul_eq_mul_mul_iff`. -/
abbrev arena : Arena where
  signature := Reg.D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity.Translation.signature
  Law r := ∀ p q p' q' : unitary ℍ[ℝ],
    (∀ x : unitary ℍ[ℝ], r.readout () ⟨p, q⟩ x = p' * x * q') ↔
      (p' = p ∧ q' = q) ∨ (p' = -p ∧ q' = -q)

/-- With the identity readout, `(p, q, p', q') = (-1, 1, 1, 1)` satisfies the left side and not
the right side. -/
theorem rejected_law :
    ¬ arena.Law Reg.D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity.Translation.rejected := by
  intro h
  rcases (h (-1) 1 1 1).mp (fun x => by
      change x = 1 * x * 1
      rw [one_mul, mul_one]) with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact one_ne_neg_one h1
  · exact one_ne_neg_one h2

/-- The exact statement of the source theorem. -/
abbrev sourceStatement : Prop := type_of% @mul_mul_eq_mul_mul_iff

def source_registration : Registration arena sourceStatement where
  actual := Reg.D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity.Translation.actual
  bridge := Iff.rfl
  variation := ⟨@mul_mul_eq_mul_mul_iff,
    Reg.D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity.Translation.rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨Reg.D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity.Translation.rejected,
        fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e
      exact nomatch e
  dependence := Reg.D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity.Translation.dependence

end Parametrization

def preserves_iff_exists_mul_mul_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@preserves_iff_exists_mul_mul.{u})
      (Realization Reg.D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity.Translation.signature)
      Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionModelAutomorphism.preserves_iff_exists_mul_mul_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionModelAutomorphism.Rigidity.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Rigidity.arena.{u}⟩
  objectArena := .source ⟨Rigidity.arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Rigidity.arena.{u} ⟨Rigidity.source_registration.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Reg.D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity.Translation.signature
    (fun _ p s => p.1 * s * p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionModelAutomorphism
    definition := none
    coordinates := #[6, 7]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg", "body", "arg", "body",
        "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

def mul_mul_eq_mul_mul_iff_registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@mul_mul_eq_mul_mul_iff)
      (Realization Reg.D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity.Translation.signature)
      Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionModelAutomorphism.mul_mul_eq_mul_mul_iff_unit
  realizationName := `Reg.D5.S3.Quantum.AURICOmega.QuaternionModelAutomorphism.Parametrization.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨Parametrization.arena⟩
  objectArena := .source ⟨Parametrization.arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source Parametrization.arena ⟨Parametrization.source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize Reg.D5.S3.Quantum.AURICOmega.QuaternionTwoPointHomogeneity.Translation.signature
    (fun _ p s => p.1 * s * p.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.AURICOmega.QuaternionModelAutomorphism
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end

end Reg.D5.S3.Quantum.AURICOmega.QuaternionModelAutomorphism
