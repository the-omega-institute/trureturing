import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.EvenSignTensorObstruction
import Reg.Support.DependentFamily
import Mathlib.Algebra.Algebra.Bilinear

open _root_.D5.S3.Geometry.EvenSignTensorObstruction
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open scoped Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
namespace Reg.D5.S3.Geometry.EvenSignTensorObstruction
universe u

/-- The observation is the vanishing of the source coefficient array. -/
abbrev tensorSignature : Signature where
  Params := Type u
  State I := I → I → I → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def tensorActual : Realization tensorSignature.{u} :=
  realize tensorSignature (fun _ _ c => c = 0) (fun e => nomatch e)
def tensorRejected : Realization tensorSignature.{u} :=
  realize tensorSignature (fun _ _ _ => False) (fun e => nomatch e)

@[reducible] def tensorArena : Arena where
  signature := tensorSignature.{u}
  Law R := ∀ {I : Type u} [Fintype I] [DecidableEq I]
    (c : I → I → I → ℝ)
    (hdiag : ∀ i k, c i i k = 0)
    (hflip : ∀ p q, p ≠ q → ∀ i j k,
      c i j k = coordinateSign p q i * coordinateSign p q j *
        coordinateSign p q k * c i j k)
    (hdim : Fintype.card I ≠ 3), R.readout () I c

theorem tensorPositive : tensorArena.{u}.Law tensorActual :=
  @tensor_eq_zero_of_card_ne_three.{u}

theorem tensorNegative : ¬ tensorArena.{u}.Law tensorRejected := by
  intro h
  exact h (I := ULift.{u} Unit) 0 (by simp)
    (by intro p q hpq; exact (hpq (Subsingleton.elim p q)).elim) (by simp)

theorem tensorDependence : ObservationalDependence tensorSignature.{u} tensorActual := by
  intro i
  refine ⟨ULift.{u} Unit, 0, (fun _ _ _ => 1), ?_⟩
  change (0 = (0 : ULift.{u} Unit → ULift.{u} Unit → ULift.{u} Unit → ℝ)) ≠
    ((fun _ _ _ => (1 : ℝ)) = (0 : ULift.{u} Unit → ULift.{u} Unit → ULift.{u} Unit → ℝ))
  intro he
  have hf := he ▸ (rfl : (0 : ULift.{u} Unit → ULift.{u} Unit → ULift.{u} Unit → ℝ) = 0)
  have hv := congrFun (congrFun (congrFun hf (ULift.up ())) (ULift.up ())) (ULift.up ())
  norm_num at hv

def tensorEvidence : Registration tensorArena.{u}
    (type_of% (@tensor_eq_zero_of_card_ne_three.{u})) where
  actual := tensorActual
  bridge := Iff.rfl
  variation := ⟨tensorPositive, tensorRejected, tensorNegative⟩
  sensitivity := ⟨fun i => ⟨tensorRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, tensorNegative⟩,
    fun i => nomatch i⟩
  dependence := tensorDependence

/-- The nonzero observation is taken on the original bilinear-map carrier. -/
abbrev bilinearSignature : Signature where
  Params := Type u
  State I := (I → ℝ) →ₗ[ℝ] (I → ℝ) →ₗ[ℝ] (I → ℝ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def bilinearActual : Realization bilinearSignature.{u} :=
  realize bilinearSignature (fun _ _ B => B ≠ 0) (fun e => nomatch e)
def bilinearRejected : Realization bilinearSignature.{u} :=
  realize bilinearSignature (fun _ _ _ => True) (fun e => nomatch e)

@[reducible] def bilinearArena : Arena where
  signature := bilinearSignature.{u}
  Law R := ∀ {I : Type u} [Fintype I] [DecidableEq I]
    (B : (I → ℝ) →ₗ[ℝ] (I → ℝ) →ₗ[ℝ] (I → ℝ))
    (hskew : ∀ u v, B u v = -(B v u))
    (hequiv : ∀ R : Matrix.specialOrthogonalGroup I ℝ, ∀ u v,
      B ((R : Matrix I I ℝ) *ᵥ u) ((R : Matrix I I ℝ) *ᵥ v) =
        (R : Matrix I I ℝ) *ᵥ B u v),
    R.readout () I B → Fintype.card I = 3

theorem bilinearPositive : bilinearArena.{u}.Law bilinearActual :=
  @special_orthogonal_equivariant_bilinear_card_eq_three.{u}

theorem bilinearNegative : ¬ bilinearArena.{u}.Law bilinearRejected := by
  intro h
  have hc := h (I := ULift.{u} Unit) 0 (by simp) (by simp) True.intro
  simp at hc

theorem bilinearDependence :
    ObservationalDependence bilinearSignature.{u} bilinearActual := by
  intro i
  let M := LinearMap.mul ℝ (ULift.{u} Unit → ℝ)
  have hm : M ≠ 0 := by
    intro he
    have hh := congrArg (fun B => B (fun _ => 1) (fun _ => 1) (ULift.up ())) he
    norm_num [M, LinearMap.mul_apply_apply] at hh
  refine ⟨ULift.{u} Unit, 0, M, ?_⟩
  change ((0 : bilinearSignature.State (ULift.{u} Unit)) ≠ 0) ≠ (M ≠ 0)
  intro he
  exact (he ▸ hm) rfl

def bilinearEvidence : Registration bilinearArena.{u}
    (type_of% (@special_orthogonal_equivariant_bilinear_card_eq_three.{u})) where
  actual := bilinearActual
  bridge := Iff.rfl
  variation := ⟨bilinearPositive, bilinearRejected, bilinearNegative⟩
  sensitivity := ⟨fun i => ⟨bilinearRejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, bilinearNegative⟩,
    fun i => nomatch i⟩
  dependence := bilinearDependence

def tensorRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.EvenSignTensorObstruction.tensor_eq_zero_of_card_ne_three.{u})
    (type_of% (realize tensorSignature.{u} (fun _ _ x => x = 0)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Geometry.EvenSignTensorObstruction.tensor_eq_zero_of_card_ne_three.tensor_unit,
  realizationName := `Reg.D5.S3.Geometry.EvenSignTensorObstruction.tensorEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨tensorArena.{u}⟩,
  objectArena := .source ⟨tensorArena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source tensorArena.{u} ⟨tensorEvidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize tensorSignature.{u} (fun _ _ x => x = 0)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.EvenSignTensorObstruction, definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body"], stateBinder := 3,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

def bilinearRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.EvenSignTensorObstruction.special_orthogonal_equivariant_bilinear_card_eq_three.{u})
    (type_of% (realize bilinearSignature.{u} (fun _ _ x => x ≠ 0)
      (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.Geometry.EvenSignTensorObstruction.special_orthogonal_equivariant_bilinear_card_eq_three.bilinear_unit,
  realizationName := `Reg.D5.S3.Geometry.EvenSignTensorObstruction.bilinearEvidence,
  realizationSource := none,
  generated := false,
  arena := .source ⟨bilinearArena.{u}⟩,
  objectArena := .source ⟨bilinearArena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source bilinearArena.{u} ⟨bilinearEvidence.{u}⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize bilinearSignature.{u} (fun _ _ x => x ≠ 0)
    (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.EvenSignTensorObstruction, definition := none, coordinates := #[0],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain"], stateBinder := 3,
      functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

#print axioms tensorRegistration
#print axioms bilinearRegistration

end Reg.D5.S3.Geometry.EvenSignTensorObstruction
