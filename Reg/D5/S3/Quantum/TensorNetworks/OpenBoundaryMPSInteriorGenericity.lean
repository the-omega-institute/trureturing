import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorGenericity

/-! Full source telescope with the actual state-function equality readout.
All polynomial, topology, actualness and environment quantifiers are retained. -/

noncomputable section
open Set Matrix MvPolynomial LeanInformationAudit
open scoped Matrix Topology ComplexOrder
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorGenericity
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSTwoSiteMinimality
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQ2PolynomialFiber
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSQuotient hiding coreCoordinates
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSMarginalBirationality
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSDensityRecovery
open _root_.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorCommonCore
open _root_.D5.S3.Quantum.TensorNetworks.PeriodicMPSParentIntersection (Word TwoSiteSpanning)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorGenericity

namespace IntrinsicInterior

abbrev signature : Signature where
  Params := ℕ
  State m := Word (3 + m) → ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ m := (Word (3 + m) → ℂ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ f g => f = g) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law T := ∀ m : ℕ, 2 ≤ m →
  ∃ R : MvPolynomial (ObsIndex ⊕ ObsIndex) ℝ, R ≠ 0 ∧
    (actualPrincipalLocus m R).Nonempty ∧ IsOpen (actualPrincipalLocus m R) ∧
    Dense (actualPrincipalLocus m R) ∧
    (∀ (ψ : openBoundaryMPS (3 + m)) (z : ℂ), ‖z‖ = 1 →
      ∃ hz : z • (ψ : Word (3 + m) → ℂ) ∈ openBoundaryMPS (3 + m),
        (⟨z • (ψ : Word (3 + m) → ℂ), hz⟩ ∈ actualPrincipalLocus m R ↔
          ψ ∈ actualPrincipalLocus m R)) ∧
    ∀ ψ : openBoundaryMPS (3 + m), ψ ∈ actualPrincipalLocus m R →
      let x := quotientCoordinates13 (quotientCoordinates m (rawPrefix 3 m ψ))
      let θ := positiveRepresentative x
      0 < sigma x ∧
      (∃ z : ℂ, ‖z‖ = 1 ∧ T.readout () m (ψ : Word (3 + m) → ℂ) (z • state (3 + m) θ)) ∧
      TwoSiteSpanning (core θ) ∧ Function.Injective (transfer (core θ)) ∧
      (∀ k : ℕ, 1 ≤ k →
        ((dualTransfer (core θ))^[k] (vecMulVec (star (left θ)) (left θ))).PosDef ∧
        ((transfer (core θ))^[k] (vecMulVec (right θ) (star (right θ)))).PosDef) ∧
      ∀ p q : ℕ, 1 ≤ p → 1 ≤ q → p + q = m →
        ∀ h : ((p + 3) + q) = 3 + m, ∀ φ : openBoundaryMPS (3 + m),
          rawInterior p 3 q (castState h φ) = rawInterior p 3 q (castState h ψ) ↔
            ∃ z : ℂ, ‖z‖ = 1 ∧ T.readout () m (φ : Word (3 + m) → ℂ) (z • (ψ : Word (3 + m) → ℂ))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  obtain ⟨R, _, hnonempty, _, _, _, hpoint⟩ := h 2 (by omega)
  obtain ⟨ψ, hψ⟩ := hnonempty
  obtain ⟨_, ⟨z, _, hf⟩, _⟩ := hpoint ψ hψ
  exact hf

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 0, 1, ?_⟩
  intro h
  have he : (1 : Word 5 → ℂ) = 0 := Eq.mp (congrFun h 0) rfl
  have hv := congrFun he (fun _ => 0)
  norm_num at hv

def family : Registration arena (type_of% (@intrinsic_interior_recovery)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@intrinsic_interior_recovery, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@intrinsic_interior_recovery) (Realization signature) Unit Unit where
  unitName :=
    `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorGenericity.intrinsic_interior_recovery.__information_unit
  realizationName :=
    `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorGenericity.IntrinsicInterior.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ f g => f = g) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorGenericity
    definition := none
    coordinates := #[0]
    readouts := #[] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
end IntrinsicInterior
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
namespace positive_iterates
abbrev signature : Signature where
  Params := Unit
  State _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ _ p => p) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := obs.readout () () (type_of% @positive_iterates)
private lemma rejected_law : ¬ arena.Law rejected := by
  intro h; exact h
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),False,True,?_⟩
  intro h
  exact (Eq.mp h.symm True.intro)
def source_registration : Registration arena (type_of% @positive_iterates) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@positive_iterates,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@positive_iterates) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorGenericity.positive_iterates.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorGenericity.positive_iterates.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end positive_iterates
namespace cast_mps
abbrev signature : Signature where
  Params := Unit
  State _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ _ p => p) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := obs.readout () () (type_of% @cast_mps)
private lemma rejected_law : ¬ arena.Law rejected := by
  intro h; exact h
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),False,True,?_⟩
  intro h
  exact (Eq.mp h.symm True.intro)
def source_registration : Registration arena (type_of% @cast_mps) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@cast_mps,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@cast_mps) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorGenericity.cast_mps.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorGenericity.cast_mps.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end cast_mps

namespace rawInterior_phase
abbrev signature : Signature where
  Params := Unit
  State _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ _ p => p) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := obs.readout () () (type_of% @rawInterior_phase)
private lemma rejected_law : ¬ arena.Law rejected := by
  intro h; exact h
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),False,True,?_⟩
  intro h
  exact (Eq.mp h.symm True.intro)
def source_registration : Registration arena (type_of% @rawInterior_phase) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rawInterior_phase,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@rawInterior_phase) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorGenericity.rawInterior_phase.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorGenericity.rawInterior_phase.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end rawInterior_phase

namespace actual_phase
abbrev signature : Signature where
  Params := Unit
  State _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ _ p => p) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := obs.readout () () (type_of% @actual_phase)
private lemma rejected_law : ¬ arena.Law rejected := by
  intro h; exact h
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),False,True,?_⟩
  intro h
  exact (Eq.mp h.symm True.intro)
def source_registration : Registration arena (type_of% @actual_phase) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@actual_phase,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@actual_phase) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorGenericity.actual_phase.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorGenericity.actual_phase.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end actual_phase

namespace locus_phase
abbrev signature : Signature where
  Params := Unit
  State _ := Prop
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature := realize signature (fun _ _ p => p) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature
  Law obs := obs.readout () () (type_of% @locus_phase)
private lemma rejected_law : ¬ arena.Law rejected := by
  intro h; exact h
private lemma dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(),False,True,?_⟩
  intro h
  exact (Eq.mp h.symm True.intro)
def source_registration : Registration arena (type_of% @locus_phase) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@locus_phase,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩
    · intro e; exact nomatch e
  dependence := dependence
def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@locus_phase) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorGenericity.locus_phase.__information_unit
  realizationName := `Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorGenericity.locus_phase.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ p => p) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }
end locus_phase

end Reg.D5.S3.Quantum.TensorNetworks.OpenBoundaryMPSInteriorGenericity
