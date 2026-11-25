import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Measurement.Auric.UnequalBlockTraceCertificates
import Reg.D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects
import Reg.Support.SingleDependentReadout

/-! Source-bound readouts for strict-trace entropy certificates. -/

namespace Reg.D5.S3.Quantum.Measurement.Auric.UnequalBlockTraceCertificates

open _root_.D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects
open _root_.Reg.D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects (signature actual rejected dependence)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

universe u

set_option autoImplicit false

noncomputable section

private def strictCaps : Fin 3 → ℕ := fun _ => 3
private def strictTraces : Fin 3 → ℝ := fun _ => 1

private theorem strictCap : ∑ j, (3 - strictCaps j) ≤ (3 : ℕ) := by
  simp [strictCaps]

private theorem strictPos (j : Fin 3) : 0 < strictTraces j := by
  norm_num [strictTraces]

private theorem strictUpper (j : Fin 3) : strictTraces j < (3 : ℝ) - (3 - strictCaps j : ℕ) := by
  norm_num [strictCaps, strictTraces]

private theorem strictTotal : ∑ j, strictTraces j = (3 : ℝ) := by
  norm_num [strictTraces, Fin.sum_univ_three]

private abbrev strictDirectArena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (m : Fin 3 → ℕ) (τ : Fin 3 → ℝ)
    (_ : ∑ j, (Fintype.card n - m j) ≤ Fintype.card n)
    (_ : ∀ j, 0 < τ j)
    (_ : ∀ j, τ j < (Fintype.card n : ℝ) - (Fintype.card n - m j : ℕ))
    (_ : ∑ j, τ j = Fintype.card n),
    ∃ (e : Equiv.Perm (Fin 3)) (w : Fin 3 → ℝ), Antitone w ∧
      R.readout () () {v : ℝ | ∃ A : Fin 3 → Matrix n n ℂ, ∃ hA : Feasible m τ A,
        spectralSum Real.negMulLog A hA.1 = v}
        (allocationValue Real.negMulLog (fun j => Fintype.card n - m (e j))
          (Fintype.card n - ∑ j, (Fintype.card n - m j)) (weightEntries w))

private theorem strictDirectRejected : ¬ strictDirectArena.{u}.Law rejected := by
  intro h
  obtain ⟨_, _, _, noMaximum⟩ :=
    h (n := ULift.{u} (Fin 3)) strictCaps strictTraces
      (by simpa using strictCap) strictPos (by simpa using strictUpper)
      (by simpa using strictTotal)
  exact noMaximum

def strictDirectRegistration : Registration strictDirectArena.{u} (type_of% @exists_isGreatest_direct.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_isGreatest_direct.{u}, rejected, strictDirectRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    strictDirectArena.{u}.Law actual rejected strictDirectRejected
  dependence := dependence

def strictDirectAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_isGreatest_direct.{u}) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects.exists_isGreatest_direct.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.Auric.UnequalBlockTraceCertificates.strictDirectRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨strictDirectArena.{u}⟩
  objectArena := .source ⟨strictDirectArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source strictDirectArena.{u} ⟨strictDirectRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s x => IsGreatest s x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.Auric.UnequalBlockTraceCertificates
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev strictComplementArena : Arena where
  signature := signature
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n]
    (m : Fin 3 → ℕ) (τ : Fin 3 → ℝ)
    (_ : ∑ j, (Fintype.card n - m j) ≤ Fintype.card n)
    (_ : ∀ j, 0 < τ j)
    (_ : ∀ j, τ j < (Fintype.card n : ℝ) - (Fintype.card n - m j : ℕ))
    (_ : ∑ j, τ j = Fintype.card n),
    ∃ (e : Equiv.Perm (Fin 3)) (w : Fin 3 → ℝ) (k : Fin 4 → ℝ), Monotone k ∧
      R.readout () () {v : ℝ | ∃ A : Fin 3 → Matrix n n ℂ, ∃ hA : Feasible m τ A,
        spectralSum (fun x => Real.negMulLog (1 - x)) A hA.1 = v}
        (allocationValue (fun x => Real.negMulLog (1 - x)) (fun j => Fintype.card n - m (e j))
          (Fintype.card n - ∑ j, (Fintype.card n - m j)) (complementEntries w k))

private theorem strictComplementRejected : ¬ strictComplementArena.{u}.Law rejected := by
  intro h
  obtain ⟨_, _, _, _, noMaximum⟩ :=
    h (n := ULift.{u} (Fin 3)) strictCaps strictTraces
      (by simpa using strictCap) strictPos (by simpa using strictUpper)
      (by simpa using strictTotal)
  exact noMaximum

def strictComplementRegistration : Registration strictComplementArena.{u} (type_of% @exists_isGreatest_complement.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_isGreatest_complement.{u}, rejected, strictComplementRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    strictComplementArena.{u}.Law actual rejected strictComplementRejected
  dependence := dependence

def strictComplementAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_isGreatest_complement.{u}) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects.exists_isGreatest_complement.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.Auric.UnequalBlockTraceCertificates.strictComplementRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨strictComplementArena.{u}⟩
  objectArena := .source ⟨strictComplementArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source strictComplementArena.{u} ⟨strictComplementRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ s x => IsGreatest s x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.Auric.UnequalBlockTraceCertificates
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "body", "arg", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev massSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

private def massActual : Realization massSignature :=
  realize massSignature (fun _ _ x y => x = y) (fun e => nomatch e)

private def massRejected : Realization massSignature :=
  realize massSignature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem massDependence : ObservationalDependence massSignature massActual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he : (0 : ℝ) = 0 ↔ (1 : ℝ) = 0 := Iff.of_eq (congrFun h 0)
  exact one_ne_zero (he.mp rfl)

private abbrev directCertificateArena : Arena where
  signature := massSignature
  Law R := ∀ (d : ℕ) (m : Fin 3 → ℕ) (τ : Fin 3 → ℝ)
    (_ : ∑ j, (d - m j) ≤ d)
    (_ : ∀ j, 0 < τ j) (_ : ∀ j, τ j < (d : ℝ) - (d - m j : ℕ))
    (_ : ∑ j, τ j = d),
    ∃ w : Fin 3 → ℝ, (∀ j, 0 < w j) ∧ (∑ j, w j = 1) ∧
      ∀ j, R.readout () () (weightMass (fun j => d - m j) (d - ∑ i, (d - m i)) w j) (τ j)

private theorem directCertificateRejected : ¬ directCertificateArena.Law massRejected := by
  intro h
  obtain ⟨_, _, _, noMass⟩ :=
    h 3 strictCaps strictTraces strictCap strictPos strictUpper strictTotal
  exact noMass 0

def directCertificateRegistration : Registration directCertificateArena (type_of% exists_direct_certificate) where
  actual := massActual
  bridge := Iff.rfl
  variation := ⟨exists_direct_certificate, massRejected, directCertificateRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    directCertificateArena.Law massActual massRejected directCertificateRejected
  dependence := massDependence

def directCertificateAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (exists_direct_certificate) (Realization massSignature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects.exists_direct_certificate.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.Auric.UnequalBlockTraceCertificates.directCertificateRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨directCertificateArena⟩
  objectArena := .source ⟨directCertificateArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source directCertificateArena ⟨directCertificateRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize massSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.Auric.UnequalBlockTraceCertificates
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body",
        "arg", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

private abbrev complementCertificateArena : Arena where
  signature := massSignature
  Law R := ∀ (d : ℕ) (m : Fin 3 → ℕ) (τ : Fin 3 → ℝ)
    (_ : ∑ j, (d - m j) ≤ d)
    (_ : ∀ j, 0 < τ j) (_ : ∀ j, τ j < (d : ℝ) - (d - m j : ℕ))
    (_ : ∑ j, τ j = d),
    ∃ (w : Fin 3 → ℝ) (k : Fin 4 → ℝ), (∀ j, 0 < w j) ∧ (∀ c, 0 < k c) ∧
      (∀ c, ∑ j, allocation (complementEntries w k) j c = 1) ∧
      ∀ j, R.readout () () (∑ c, (multiplicity (fun j => d - m j) (d - ∑ i, (d - m i)) c : ℝ) *
        allocation (complementEntries w k) j c) (τ j)

private theorem complementCertificateRejected : ¬ complementCertificateArena.Law massRejected := by
  intro h
  obtain ⟨_, _, _, _, _, noMass⟩ :=
    h 3 strictCaps strictTraces strictCap strictPos strictUpper strictTotal
  exact noMass 0

def complementCertificateRegistration : Registration complementCertificateArena (type_of% exists_complement_certificate) where
  actual := massActual
  bridge := Iff.rfl
  variation := ⟨exists_complement_certificate, massRejected, complementCertificateRejected⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    complementCertificateArena.Law massActual massRejected complementCertificateRejected
  dependence := massDependence

def complementCertificateAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (exists_complement_certificate) (Realization massSignature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Measurement.Auric.UnequalBlockEffects.exists_complement_certificate.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Measurement.Auric.UnequalBlockTraceCertificates.complementCertificateRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨complementCertificateArena⟩
  objectArena := .source ⟨complementCertificateArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source complementCertificateArena ⟨complementCertificateRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize massSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Measurement.Auric.UnequalBlockTraceCertificates
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "arg", "body",
        "arg", "body", "arg", "arg", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms strictDirectAudit
#print axioms strictComplementAudit
#print axioms directCertificateAudit
#print axioms complementCertificateAudit

end
end Reg.D5.S3.Quantum.Measurement.Auric.UnequalBlockTraceCertificates
