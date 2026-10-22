import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.BcGhostFockCommutant
import Reg.Support.DependentFamily

set_option autoImplicit false

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.BcGhostFockSupport
open _root_.D5.S3.VertexAlgebra.BcGhostFockCommutant

namespace Reg.D5.S3.VertexAlgebra.BcGhostFockCommutant

universe u

namespace Kernel

structure Parameters where
  K : Type u
  ring : CommRing K
  site : ℕ

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := letI := p.ring; Fock p.K
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := letI := p.ring; Fock p.K
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p v => letI := p.ring; annihilate p.site v)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => letI := p.ring; 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (K : Type u) (ring : CommRing K), letI := ring
    ∀ v : Fock K,
      (∀ i : ℕ, R.readout () (⟨K, ring, i⟩ : Parameters.{u}) v = 0) ↔
        v = v ∅ • (vacuum : Fock K)

abbrev SourceClaim : Prop :=
  ∀ {K : Type u} [CommRing K] (v : Fock K),
    (∀ i : ℕ, annihilate i v = 0) ↔ v = v ∅ • vacuum

theorem rejectedLaw : ¬ arena.{u}.Law rejected.{u} := by
  classical
  intro h
  let K := ULift.{u} ℤ
  let v : Fock K := Finsupp.single {0} 1
  have hv := (h K inferInstance v).mp (by intro i; rfl)
  have he := congrArg (fun w : Fock K => w {0}) hv
  simp [v, vacuum] at he

theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  classical
  intro role
  let p : Parameters.{u} := ⟨ULift.{u} ℤ, inferInstance, 0⟩
  letI := p.ring
  refine ⟨p, 0, Finsupp.single {0} 1, ?_⟩
  intro h
  have he := congrArg (fun w : Fock p.K => w ∅) h
  simp [actual, realize, p, annihilate, Finsupp.linearCombination_single,
    annihilateBasis, sign] at he

def registration : Registration arena.{u} SourceClaim.{u} where
  actual := actual
  bridge := by
    constructor
    · intro h K ring
      letI := ring
      exact h
    · intro h K ring
      letI := ring
      exact h K ring
  variation := ⟨by intro K ring; letI := ring; exact annihilator_kernel, rejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejectedLaw⟩
      intro other hne
      exact (hne (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def audit : Contract.Registration
    (@annihilator_kernel.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.BcGhostFockCommutant.annihilator_kernel.Kernel
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostFockCommutant.Kernel.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p v => letI := p.ring; annihilate p.site v)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BcGhostFockCommutant
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end Kernel

namespace Commutant

structure Parameters where
  K : Type u
  ring : CommRing K

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := letI := p.ring; Module.End p.K (Fock p.K)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := letI := p.ring; Fock p.K
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p T => letI := p.ring; T vacuum) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => letI := p.ring; 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (K : Type u) (ring : CommRing K), letI := ring
    ∀ (T : Module.End K (Fock K)),
      (∀ m : ℤ, T.comp (b m) = (b m).comp T) →
      (∀ n : ℤ, T.comp (c n) = (c n).comp T) →
      T = (R.readout () (⟨K, ring⟩ : Parameters.{u}) T) ∅ •
        (LinearMap.id : Module.End K (Fock K))

abbrev SourceClaim : Prop :=
  ∀ {K : Type u} [CommRing K] (T : Module.End K (Fock K)),
    (∀ m : ℤ, T.comp (b m) = (b m).comp T) →
    (∀ n : ℤ, T.comp (c n) = (c n).comp T) →
    T = (T vacuum) ∅ • LinearMap.id

theorem rejectedLaw : ¬ arena.{u}.Law rejected.{u} := by
  classical
  intro h
  let K := ULift.{u} ℤ
  have hz := h K inferInstance LinearMap.id (by intro m; simp) (by intro n; simp)
  have he := congrArg (fun T : Module.End K (Fock K) => (T vacuum) ∅) hz
  simp [rejected, realize, vacuum] at he

theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  classical
  intro role
  let p : Parameters.{u} := ⟨ULift.{u} ℤ, inferInstance⟩
  letI := p.ring
  refine ⟨p, 0, LinearMap.id, ?_⟩
  intro h
  have he := congrArg (fun w : Fock p.K => w ∅) h
  simp [actual, realize, p, vacuum] at he

def registration : Registration arena.{u} SourceClaim.{u} where
  actual := actual
  bridge := by
    constructor
    · intro h K ring
      letI := ring
      exact h
    · intro h K ring
      letI := ring
      exact h K ring
  variation := ⟨by intro K ring; letI := ring; exact mode_commutant_scalar, rejected, rejectedLaw⟩
  sensitivity := by
    constructor
    · intro role
      refine ⟨rejected, ?_, rfl, rejectedLaw⟩
      intro other hne
      exact (hne (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def audit : Contract.Registration
    (@mode_commutant_scalar.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.BcGhostFockCommutant.mode_commutant_scalar.Commutant
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostFockCommutant.Commutant.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p T => letI := p.ring; T vacuum)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BcGhostFockCommutant
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end Commutant

end Reg.D5.S3.VertexAlgebra.BcGhostFockCommutant
