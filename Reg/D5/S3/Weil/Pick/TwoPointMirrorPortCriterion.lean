import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Weil.Pick.TwoPointMirrorPortCriterion
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Matrix
open scoped ComplexOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Pick.TwoPointMirrorPortCriterion

namespace Reg.D5.S3.Weil.Pick.TwoPointMirrorPortCriterion

universe u

structure Params where
  Port : Type u
  finitePort : Fintype Port
  decidablePort : DecidableEq Port
  pole : ℂ
  samples : Fin 2 → ℂ

def signature : Signature where
  Params := Params.{u}
  State p := Matrix p.Port p.Port ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Matrix (p.Port ⊕ p.Port) (p.Port ⊕ p.Port) ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature
    (fun _ p C => @mirrorNevanlinnaGram p.Port p.finitePort p.decidablePort
      p.pole C p.samples)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {Port : Type u} [fp : Fintype Port] [dp : DecidableEq Port]
    (mu : ℂ) (C : Matrix Port Port ℂ) (z : Fin 2 → ℂ)
    (_ : mu ≠ star mu) (_ : z 0 ≠ z 1) (_ : ∀ i, 0 < (z i).im)
    (_ : ∀ i, mu - z i ≠ 0 ∧ star mu - z i ≠ 0),
      (R.readout () ⟨Port, fp, dp, mu, z⟩ C).PosSemidef ↔ C = 0

private def samples : Fin 2 → ℂ := ![2 * Complex.I, 3 * Complex.I]

private theorem pole_nonreal : Complex.I ≠ star Complex.I := by
  norm_num [Complex.ext_iff]

private theorem samples_distinct : samples 0 ≠ samples 1 := by
  norm_num [samples, Complex.ext_iff]

private theorem samples_upper (i : Fin 2) : 0 < (samples i).im := by
  fin_cases i <;> norm_num [samples]

private theorem samples_regular (i : Fin 2) :
    Complex.I - samples i ≠ 0 ∧ star Complex.I - samples i ≠ 0 := by
  fin_cases i <;> constructor <;> norm_num [samples, Complex.ext_iff]

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h (Port := ULift.{u} Unit) Complex.I 1 samples
    pole_nonreal samples_distinct samples_upper samples_regular
  change (0 : Matrix (ULift.{u} Unit ⊕ ULift.{u} Unit)
    (ULift.{u} Unit ⊕ ULift.{u} Unit) ℂ).PosSemidef ↔
      (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) = 0 at hh
  exact one_ne_zero (hh.mp Matrix.PosSemidef.zero)

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  let p : Params.{u} := ⟨ULift.{u} Unit, inferInstance, inferInstance,
    Complex.I, samples⟩
  refine ⟨p, 0, 1, ?_⟩
  change mirrorNevanlinnaGram Complex.I (0 : Matrix p.Port p.Port ℂ) samples ≠
    mirrorNevanlinnaGram Complex.I (1 : Matrix p.Port p.Port ℂ) samples
  have hz : mirrorNevanlinnaGram Complex.I (0 : Matrix p.Port p.Port ℂ) samples = 0 := by
    simp [mirrorNevanlinnaGram, mirrorNevanlinnaBlock, mirrorResolvent]
  rw [hz]
  intro he
  have hp : (mirrorNevanlinnaGram Complex.I (1 : Matrix p.Port p.Port ℂ)
      samples).PosSemidef := by
    rw [← he]
    exact Matrix.PosSemidef.zero
  exact one_ne_zero ((two_point_mirror_posSemidef_iff Complex.I
    (1 : Matrix p.Port p.Port ℂ) samples pole_nonreal samples_distinct
    samples_upper samples_regular).mp hp)

def source : Registration arena.{u} (type_of% @two_point_mirror_posSemidef_iff.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@two_point_mirror_posSemidef_iff, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration
    (@two_point_mirror_posSemidef_iff.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Weil.Pick.TwoPointMirrorPortCriterion.unit
  realizationName := `Reg.D5.S3.Weil.Pick.TwoPointMirrorPortCriterion.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p C => @mirrorNevanlinnaGram p.Port p.finitePort p.decidablePort
      p.pole C p.samples) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Pick.TwoPointMirrorPortCriterion
    definition := none
    coordinates := #[0, 3, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

namespace Congruence

open _root_.D5.S3.SpectralTopology.FiniteSpectralLocalizer

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {Port : Type u} [fp : Fintype Port] [dp : DecidableEq Port]
    (mu : ℂ) (C : Matrix Port Port ℂ) (z : Fin 2 → ℂ)
    (_ : mu ≠ star mu) (_ : z 0 ≠ z 1) (_ : ∀ i, 0 < (z i).im)
    (_ : ∀ i, mu - z i ≠ 0 ∧ star mu - z i ≠ 0),
      R.readout () ⟨Port, fp, dp, mu, z⟩ C =
          mirrorCauchyFeature mu z *
            finiteSpectralLocalizer (0 : Matrix Port Port ℂ) C 0 0 0 *
              (mirrorCauchyFeature mu z)ᴴ ∧
        IsUnit (mirrorCauchyFeature (Port := Port) mu z)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h (Port := ULift.{u} Unit) Complex.I 1 samples
    pole_nonreal samples_distinct samples_upper samples_regular
  have hf := (two_point_mirror_congruence Complex.I
    (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) samples pole_nonreal
    samples_distinct samples_upper samples_regular).1
  have hz : mirrorNevanlinnaGram Complex.I
      (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) samples = 0 :=
    hf.trans hh.1.symm
  have hp : (mirrorNevanlinnaGram Complex.I
      (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) samples).PosSemidef := by
    rw [hz]
    exact Matrix.PosSemidef.zero
  exact one_ne_zero ((two_point_mirror_posSemidef_iff Complex.I
    (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) samples pole_nonreal
    samples_distinct samples_upper samples_regular).mp hp)

def source : Registration arena.{u} (type_of% @two_point_mirror_congruence.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@two_point_mirror_congruence, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration
    (@two_point_mirror_congruence.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Weil.Pick.TwoPointMirrorPortCriterion.Congruence.unit
  realizationName := `Reg.D5.S3.Weil.Pick.TwoPointMirrorPortCriterion.Congruence.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p C => @mirrorNevanlinnaGram p.Port p.finitePort p.decidablePort
      p.pole C p.samples) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Pick.TwoPointMirrorPortCriterion
    definition := none
    coordinates := #[0, 3, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end Congruence

namespace Sparse

def arena : Arena where
  signature := signature.{u}
  Law R := ∀ {Port : Type u} [fp : Fintype Port] [dp : DecidableEq Port]
    (mu : ℂ) (C : Matrix Port Port ℂ) (z : Fin 2 → ℂ)
    (_ : mu ≠ star mu) (_ : z 0 ≠ z 1) (_ : ∀ i, 0 < (z i).im)
    (_ : ∀ i, mu - z i ≠ 0 ∧ star mu - z i ≠ 0),
      let G := R.readout () ⟨Port, fp, dp, mu, z⟩ C
      C ≠ 0 ↔ ∃ p q : Port ⊕ Port, p ≠ q ∧
        (G p p * G q q - G p q * G q p).re < 0

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨p, q, _, hneg⟩ := (h (Port := ULift.{u} Unit) Complex.I 1 samples
    pole_nonreal samples_distinct samples_upper samples_regular).mp one_ne_zero
  change ((0 : ℂ) * 0 - 0 * 0).re < 0 at hneg
  norm_num at hneg

def source : Registration arena.{u}
    (type_of% @two_point_mirror_negative_principal_minor.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@two_point_mirror_negative_principal_minor, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro other hne
      exact (hne (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

def registration : LeanInformationAudit.Contract.Registration
    (@two_point_mirror_negative_principal_minor.{u})
    (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Weil.Pick.TwoPointMirrorPortCriterion.Sparse.unit
  realizationName := `Reg.D5.S3.Weil.Pick.TwoPointMirrorPortCriterion.Sparse.source
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ p C => @mirrorNevanlinnaGram p.Port p.finitePort p.decidablePort
      p.pole C p.samples) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Pick.TwoPointMirrorPortCriterion
    definition := none
    coordinates := #[0, 3, 5]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "value"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration

end Sparse

end Reg.D5.S3.Weil.Pick.TwoPointMirrorPortCriterion
