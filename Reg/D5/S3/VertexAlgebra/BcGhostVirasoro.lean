import LeanInformationAuditInterface.Contract.Registration
import D5.S3.VertexAlgebra.BcGhostVirasoro
import Reg.Support.DependentFamily

set_option autoImplicit false

noncomputable section

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.BcGhostFockSupport
open _root_.D5.S3.VertexAlgebra.BcGhostVacuum
open _root_.D5.S3.VertexAlgebra.BcGhostVirasoro

namespace Reg.D5.S3.VertexAlgebra.BcGhostVirasoro

universe u

structure Parameters where
  K : Type u
  ring : CommRing K
  m : ℤ

abbrev signature : Signature where
  Params := Parameters.{u}
  State _ := ℤ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := letI := p.ring; Module.End p.K (Fock p.K)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p n => letI := p.ring; L n) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p _ => letI := p.ring; 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (K : Type u) (ring : CommRing K), letI := ring
    ∀ m n : ℤ,
      L m * R.readout () (⟨K, ring, m⟩ : Parameters.{u}) n -
        R.readout () (⟨K, ring, m⟩ : Parameters.{u}) n * L m =
      (m - n : K) • L (m + n) +
        (if m + n = 0 then ((-13 * (m ^ 3 - m) / 6 : ℤ) : K) else 0) • LinearMap.id

abbrev SourceClaim : Prop :=
  ∀ {K : Type u} [CommRing K] (m n : ℤ),
    L (K := K) m * L n - L n * L m =
      (m - n : K) • L (m + n) +
        (if m + n = 0 then ((-13 * (m ^ 3 - m) / 6 : ℤ) : K) else 0) • LinearMap.id

theorem rejectedLaw : ¬ arena.{u}.Law rejected.{u} := by
  classical
  intro h
  let K := ULift.{u} ℤ
  have he := congrArg (fun T : Module.End K (Fock K) => (T vacuum) ∅)
    (h K inferInstance 2 (-2))
  have hzero := L_vacuum_annihilation (K := K) 0 (by omega)
  simp only [vacuum] at hzero
  norm_num [rejected, realize, LinearMap.smul_apply, LinearMap.add_apply,
    Module.End.mul_apply, hzero, vacuum] at he
  have heInt := congrArg (fun value : ULift.{u} ℤ => value.down) he
  norm_num at heInt

theorem dependence : ObservationalDependence signature.{u} actual.{u} := by
  classical
  intro role
  let p : Parameters.{u} := ⟨ULift.{u} ℤ, inferInstance, 2⟩
  letI := p.ring
  refine ⟨p, 0, -2, ?_⟩
  intro h
  have he := congrArg (fun T : Module.End p.K (Fock p.K) => (L 2 (T vacuum)) ∅) h
  have hzero := L_vacuum_annihilation (K := p.K) 0 (by omega)
  have hcontract := L_vacuum_contraction (K := p.K) 2 (by omega)
  change (L (K := p.K) 2 (L 0 vacuum)) ∅ =
    (L (K := p.K) 2 (L (-2) vacuum)) ∅ at he
  rw [hzero, map_zero, hcontract] at he
  norm_num [p, vacuum] at he
  have heInt := congrArg (fun value : ULift.{u} ℤ => value.down) he
  norm_num at heInt

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
  variation := ⟨by intro K ring; letI := ring; exact L_virasoro, rejected, rejectedLaw⟩
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
    (@L_virasoro.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `D5.S3.VertexAlgebra.BcGhostVirasoro.L_virasoro.Virasoro
  realizationName := `Reg.D5.S3.VertexAlgebra.BcGhostVirasoro.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p n => letI := p.ring; L n)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.BcGhostVirasoro
    definition := none
    coordinates := #[0, 1, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end Reg.D5.S3.VertexAlgebra.BcGhostVirasoro
