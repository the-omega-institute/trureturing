import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Quantum.Dynamics.CalibratedUnitaryGroup

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Dynamics.CalibratedUnitaryGroup
noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Dynamics.CalibratedUnitaryGroup

abbrev signature : Signature where
  Params := Σ H : Type u, Σ ng : NormedAddCommGroup H,
    letI := ng; InnerProductSpace ℂ H
  State p :=
    letI := p.2.1
    letI := p.2.2
    p.1 →L[ℂ] p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p :=
    letI := p.2.1
    letI := p.2.2
    (p.1 →L[ℂ] p.1) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {H : Type u} [ng : NormedAddCommGroup H] [ip : InnerProductSpace ℂ H]
    [CompleteSpace H] (U : ℝ → H →L[ℂ] H) (G : H →L[ℂ] H),
    U 0 = 1 → (∀ s t, U (s + t) = U s * U t) →
    (∀ t, star (U t) * U t = 1) → HasDerivAt U G 0 →
    ∀ (ℏ : ℝ), ℏ ≠ 0 →
      let Hamiltonian := (Complex.I * (ℏ : ℂ)) • G
      IsSelfAdjoint Hamiltonian ∧
      (∀ t, R.readout () ⟨H, ng, ip⟩ (U t)
        (NormedSpace.exp ((-Complex.I * (t : ℂ) / (ℏ : ℂ)) • Hamiltonian))) ∧
      (∀ t, HasDerivAt U ((-Complex.I / (ℏ : ℂ)) • (Hamiltonian * U t)) t)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let H := EuclideanSpace ℂ (ULift.{u} Unit)
  have hh := h (H := H) (fun _ => 1) 0 rfl (by simp)
    (by intro t; change star (1 : H →L[ℂ] H) * 1 = 1; rw [star_one, mul_one])
    (hasDerivAt_const 0 (1 : H →L[ℂ] H)) 1 one_ne_zero
  exact hh.2.1 0

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let H := EuclideanSpace ℂ (ULift.{u} Unit)
  let p : signature.{u}.Params := ⟨H, inferInstance, inferInstance⟩
  refine ⟨p, 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  have hc : (1 : H →L[ℂ] H) = 0 := he.mp rfl
  exact one_ne_zero hc

def family : Registration arena.{u} (type_of% (@calibrated_group.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@calibrated_group, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@calibrated_group.{u})
    (type_of% (realize signature.{u} (fun _ _ x y => x = y) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S3.Quantum.Dynamics.CalibratedUnitaryGroup.calibrated_group.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.CalibratedUnitaryGroup.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.CalibratedUnitaryGroup
    definition := none
    coordinates := #[0, 1, 2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "arg", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration
end Reg.D5.S3.Quantum.Dynamics.CalibratedUnitaryGroup
