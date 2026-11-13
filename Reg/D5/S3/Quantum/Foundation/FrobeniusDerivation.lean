import D5.S3.Quantum.Foundation.FrobeniusDerivation
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

noncomputable section
universe u
open scoped InnerProductSpace RealInnerProductSpace
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Quantum.Foundation.FrobeniusDerivation
open _root_.D5.S3.Quantum.Foundation.FrobeniusDerivation

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {V : Type u} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (S : V →ₗ[ℝ] V →ₗ[ℝ] V) (e : V)
    (_comm : ∀ x y, S x y = S y x)
    (_unit : ∀ x, S e x = x)
    (_frob : ∀ x y z, ⟪S x y, z⟫_ℝ = ⟪y, S x z⟫_ℝ)
    (d : V →ₗ[ℝ] V)
    (_der : ∀ x y, d (S x y) = S (d x) y + S x (d y))
    (x y : V), R.readout () () ⟪d x, y⟫_ℝ (-⟪x, d y⟫_ℝ)

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact @h PUnit.{u+1} inferInstance inferInstance inferInstance 0 0
    (by intros; rfl) (by intros; exact Subsingleton.elim _ _)
    (by intros; simp) 0 (by intros; simp) 0 0

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  intro h
  have he := congrFun h 0
  change ((0 : ℝ) = 0) = (1 = 0) at he
  exact one_ne_zero (Eq.mp he rfl)

def family : Registration arena.{u} (type_of% @derivation_skew_adjoint.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@derivation_skew_adjoint.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@derivation_skew_adjoint.{u}) (Realization signature) Unit Unit where
  unitName := `D5.S3.Quantum.Foundation.FrobeniusDerivation.derivation_skew_adjoint.audit
  realizationName := `Reg.D5.S3.Quantum.Foundation.FrobeniusDerivation.family
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
    owner := `D5.S3.Quantum.Foundation.FrobeniusDerivation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit

end Reg.D5.S3.Quantum.Foundation.FrobeniusDerivation
