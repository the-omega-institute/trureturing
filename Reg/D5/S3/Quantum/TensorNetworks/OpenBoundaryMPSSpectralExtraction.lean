import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSSpectralExtraction
import Reg.Support.DependentFamily

/-! Faithful full-statement source-family attempts. The source-selection binding
remains unsubmitted under issue #30422; kernel-checked family laws do not imply
native audit validation. -/
set_option autoImplicit false
noncomputable section
namespace Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSSpectralExtraction
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSSpectralExtraction
open _root_.D5.S3.Quantum.TensorNetworks
open _root_.D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection (Bond Word)
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality (mpsState)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open Matrix
open scoped Matrix

namespace spectral_frame
abbrev signature : Signature where
  Params := Unit
  State _ := ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (ℂ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {c : Fin 5 → ℂ} {e : ℂ} (hc : Admissible c e),
    obs.readout () () (T c e).det e ∧ L c ᵥ* T c e = ![1, 1] ∧
    (A c 1 * (A c 0)⁻¹) * T c e = T c e * diagonal ![lam c e, mu c e] ∧
    (K c e).det = -c 2 ∧
    u c e * t c e = c 2 * U c / D c ∧
    v c e * w c e = c 2 * (U c + D c) / D c ∧
    u c e ≠ 0 ∧ v c e ≠ 0 ∧ w c e ≠ 0 ∧ t c e ≠ 0 ∧ gap c e ≠ 0

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h (c := witnessC) (e := 1) (fixed_witness_extraction 0).1).1
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh : (1 : ℂ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hh

def source_registration : Registration arena (type_of% @spectral_frame) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@spectral_frame, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@spectral_frame) (Realization signature) (type_of% @T) Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSSpectralExtraction.spectral_frame.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSSpectralExtraction.spectral_frame.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@T)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms registration
end spectral_frame

namespace native_extraction
abbrev signature : Signature where
  Params := Unit
  State _ := Fin 2 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (Fin 2 → ℂ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {c : Fin 5 → ℂ} {e : ℂ} (hc : Admissible c e),
    (S c e).det ≠ 0 ∧ z c e ≠ 0 ∧
    OpenBoundaryMPSInteriorRootRealization.delta (sector c e) = gap c e ∧
    OpenBoundaryMPSInteriorRootRealization.alpha (sector c e) = offset c e ∧
    OpenBoundaryMPSInteriorRootRealization.beta (sector c e) =
      gap c e * u c e * t c e / (-c 2) ∧
    OpenBoundaryMPSInteriorRootRealization.delta (sector c e) *
      OpenBoundaryMPSInteriorRootRealization.alpha (sector c e) *
      OpenBoundaryMPSInteriorRootRealization.beta (sector c e) ≠ 0 ∧
    obs.readout () () (nativeLeft c e) ![1, rho c e] ∧
    (∀ i, A c i * S c e = u c e •
      (S c e * OpenBoundaryMPSInteriorRootRealization.core (sector c e) (z c e) i)) ∧
    (OpenBoundaryMPSInteriorRootRealization.Regular (sector c e) ↔
      1 + star (lam c e) * mu c e ≠ 0) ∧
    OpenBoundaryMPSInteriorRootRealization.beta (sector c e) -
      OpenBoundaryMPSInteriorRootRealization.alpha (sector c e) = gap c e

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h (c := witnessC) (e := 1) (fixed_witness_extraction 0).1).2.2.2.2.2.2.1
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh : (1 : Fin 2 → ℂ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hh

def source_registration : Registration arena (type_of% @native_extraction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@native_extraction, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@native_extraction) (Realization signature) (type_of% @nativeLeft) Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSSpectralExtraction.native_extraction.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSSpectralExtraction.native_extraction.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@nativeLeft)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms registration
end native_extraction

namespace raw_amplitude
abbrev signature : Signature where
  Params := ℕ
  State n := Word n → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ n := (Word n → ℂ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {c : Fin 5 → ℂ} {e : ℂ} (hc : Admissible c e)
    (N : ℕ) (R : Fin 2 → ℂ),
    obs.readout () N (mpsState N (A c 0) (A c 1) (L c) R) <|
      mpsState N (OpenBoundaryMPSInteriorRootRealization.core (sector c e) (z c e) 0)
        (OpenBoundaryMPSInteriorRootRealization.core (sector c e) (z c e) 1)
        (nativeLeft c e) (nativeRight c e N R)

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h (c := witnessC) (e := 1) (fixed_witness_extraction 0).1 0 0
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨0, 0, 1, ?_⟩
  intro he
  have hh : (1 : Word 0 → ℂ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hh

def source_registration : Registration arena (type_of% @raw_amplitude) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@raw_amplitude, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@raw_amplitude) (Realization signature) (type_of% @nativeRight) Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSSpectralExtraction.raw_amplitude.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSSpectralExtraction.raw_amplitude.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@nativeRight)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms registration
end raw_amplitude

namespace normalizer_inverse
abbrev signature : Signature where
  Params := Unit
  State _ := Bond
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (Bond) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {c : Fin 5 → ℂ} {e : ℂ} (hc : Admissible c e),
    obs.readout () () (leftNormalizer (sector c e) (z c e) (nativeLeft c e)) ((u c e)⁻¹ • S c e) ∧
    nativeLeft c e ᵥ* (leftNormalizer (sector c e) (z c e) (nativeLeft c e))⁻¹ =
      u c e • L c ∧
    (nativeLeft c e ᵥ* (leftNormalizer (sector c e) (z c e) (nativeLeft c e))⁻¹) 1 =
      u c e

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h (c := witnessC) (e := 1) (fixed_witness_extraction 0).1).1
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh : (1 : Bond) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hh

def source_registration : Registration arena (type_of% @normalizer_inverse) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@normalizer_inverse, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@normalizer_inverse) (Realization signature) (type_of% @leftNormalizer) Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSSpectralExtraction.normalizer_inverse.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSSpectralExtraction.normalizer_inverse.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@leftNormalizer)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms registration
end normalizer_inverse

namespace canonicalization_inverse
abbrev signature : Signature where
  Params := Unit
  State _ := Bond
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (Bond) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ {c : Fin 5 → ℂ} {e : ℂ} (hc : Admissible c e)
    (N : ℕ) (R : Fin 2 → ℂ),
    let J := leftNormalizer (sector c e) (z c e) (nativeLeft c e)
    (∀ i, obs.readout () () (u c e • (J * OpenBoundaryMPSInteriorRootRealization.core (sector c e) (z c e) i * J⁻¹)) (A c i)) ∧
    (u c e)⁻¹ • (nativeLeft c e ᵥ* J⁻¹) = L c ∧
    (u c e * (u c e ^ N)⁻¹) • (J *ᵥ nativeRight c e N R) = R

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h (c := witnessC) (e := 1) (fixed_witness_extraction 0).1 0 0).1 0
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh : (1 : Bond) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hh

def source_registration : Registration arena (type_of% @canonicalization_inverse) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@canonicalization_inverse, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@canonicalization_inverse) (Realization signature) (type_of% @leftNormalizer) Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSSpectralExtraction.canonicalization_inverse.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSSpectralExtraction.canonicalization_inverse.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@leftNormalizer)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms registration
end canonicalization_inverse

namespace fixed_witness_extraction
abbrev signature : Signature where
  Params := Unit
  State _ := Bond
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (Bond) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ (N : ℕ),
    Admissible witnessC 1 ∧ D witnessC = 1 ∧ U witnessC = -1/2 ∧
    U witnessC + D witnessC = 1/2 ∧
    obs.readout () () (T witnessC 1) !![1, 0; 1, 1] ∧
    K witnessC 1 = !![1/2, 1/2; 1/2, -(1/2)] ∧
    rho witnessC 1 = 1 ∧ sector witnessC 1 = witnessSector ∧ z witnessC 1 = 1 ∧
    nativeLeft witnessC 1 = witnessLeft ∧
    nativeRight witnessC 1 N (witnessCanonicalRight N) = witnessRight ∧
    nativeRight witnessC 1 N ![1, 1 + Complex.I] = (1/2 : ℂ) ^ N • witnessRight ∧
    1 + star (lam witnessC 1) * mu witnessC 1 = 1

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h 0).2.2.2.2.1
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh : (1 : Bond) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hh

def source_registration : Registration arena (type_of% @fixed_witness_extraction) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fixed_witness_extraction, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@fixed_witness_extraction) (Realization signature) (type_of% @witnessC) Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSSpectralExtraction.fixed_witness_extraction.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSSpectralExtraction.fixed_witness_extraction.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@witnessC)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms registration
end fixed_witness_extraction

namespace fixed_witness_quotient_boundary
abbrev signature : Signature where
  Params := Unit
  State _ := Fin 2 → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := (Fin 2 → ℂ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := ∀ (N : ℕ),
    obs.readout () () (OpenBoundaryMPSQuotient.positiveBoundary (witnessC, (4 : ℝ)^N, 1 + Complex.I)) (witnessCanonicalRight N) ∧
    Complex.normSq (witnessCanonicalRight N 0) = (4 : ℝ)^N ∧
    witnessCanonicalRight N 1 / witnessCanonicalRight N 0 = 1 + Complex.I ∧
    mpsState N (A witnessC 0) (A witnessC 1) (L witnessC)
      (OpenBoundaryMPSQuotient.positiveBoundary (witnessC, (4 : ℝ)^N, 1 + Complex.I)) =
    mpsState N (OpenBoundaryMPSInteriorRootRealization.core witnessSector 1 0)
      (OpenBoundaryMPSInteriorRootRealization.core witnessSector 1 1) witnessLeft witnessRight

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  exact (h 0).1
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro he
  have hh : (1 : Fin 2 → ℂ) = 0 := Eq.mp (congrFun he 0) rfl
  exact one_ne_zero hh

def source_registration : Registration arena (type_of% @fixed_witness_quotient_boundary) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@fixed_witness_quotient_boundary, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@fixed_witness_quotient_boundary) (Realization signature) (type_of% @witnessCanonicalRight) Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSSpectralExtraction.fixed_witness_quotient_boundary.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSSpectralExtraction.fixed_witness_quotient_boundary.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ X Y => X = Y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some (@witnessCanonicalRight)
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms registration
end fixed_witness_quotient_boundary

end Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSSpectralExtraction
