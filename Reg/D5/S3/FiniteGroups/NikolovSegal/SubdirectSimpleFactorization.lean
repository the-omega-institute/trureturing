import LeanInformationAuditInterface.Contract.Registration
import D5.S3.FiniteGroups.NikolovSegal.SubdirectSimpleFactorization
import Reg.Support.DependentFamily
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple
import Mathlib.Algebra.Group.ULift

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.FiniteGroups.NikolovSegal.SubdirectSimpleFactorization
universe u v w

structure SourceData where
  I : Type u
  finiteI : Finite I
  A : I → Type v
  groupA : ∀ i, Group (A i)
  F : Type w
  groupF : Group F
  simpleF : @IsSimpleGroup F groupF
  noncomm : letI := groupF; ¬ ∀ x y : F, x * y = y * x
  B : letI := groupA; Subgroup (∀ i, A i)
  onto : by
    letI := groupA
    exact ∀ i, Function.Surjective ((Pi.evalMonoidHom A i).comp B.subtype)
  theta : by
    letI := groupA
    letI := groupF
    exact B →* F
  theta_onto : Function.Surjective theta

abbrev signature : Signature where
  Params := SourceData.{u,v,w}
  State p := p.B
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.F
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u,v,w} :=
  realize signature (fun _ p b => p.theta b) (fun e => nomatch e)

def rejected : Realization signature.{u,v,w} :=
  realize signature (fun _ p b => by
    letI := p.groupF
    exact (p.theta b)⁻¹) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u,v,w}
  Law R := ∀ {I : Type u} [hI : Finite I]
    (A : I → Type v) [hA : ∀ i, Group (A i)]
    {F : Type w} [hF : Group F] [hS : IsSimpleGroup F]
    (noncomm : ¬ ∀ x y : F, x * y = y * x)
    (B : Subgroup (∀ i, A i))
    (onto : ∀ i, Function.Surjective ((Pi.evalMonoidHom A i).comp B.subtype))
    (theta : B →* F) (theta_onto : Function.Surjective theta),
    ∃ i : I, ∃ phi : A i →* F, ∀ b : B,
      R.readout () ⟨I,hI,A,hA,F,hF,hS,noncomm,B,onto,theta,theta_onto⟩ b = phi (b.val i)

abbrev statement : Prop := type_of% @NikolovSegal.subdirect_simple_factorization.{u,v,w}

theorem bridge : statement.{u,v,w} ↔ arena.{u,v,w}.Law actual := Iff.rfl

private theorem inverse_cannot_factor (p : SourceData.{u,v,w}) : by
    letI := p.groupA
    letI := p.groupF
    exact ¬ ∃ i : p.I, ∃ phi : p.A i →* p.F,
      ∀ b : p.B, (p.theta b)⁻¹ = phi (b.val i) := by
  letI := p.groupA
  letI := p.groupF
  rintro ⟨i,phi,hphi⟩
  apply p.noncomm
  intro a b
  obtain ⟨x,rfl⟩ := p.theta_onto a
  obtain ⟨y,rfl⟩ := p.theta_onto b
  have hm : (p.theta (x * y))⁻¹ = (p.theta x)⁻¹ * (p.theta y)⁻¹ := by
    rw [hphi (x * y), hphi x, hphi y]
    exact phi.map_mul (x.val i) (y.val i)
  simpa only [map_mul, mul_inv_rev, inv_inv] using congrArg Inv.inv hm

private abbrev Base := alternatingGroup (Fin 5)

private theorem base_noncomm : ¬ ∀ x y : Base, x * y = y * x := by
  intro h
  have hc : IsMulCommutative Base := ⟨⟨h⟩⟩
  have hb := alternatingGroup.isMulCommutative_iff_card_le_three.mp hc
  norm_num at hb

private def testData : SourceData.{u,v,w} := by
  let I := ULift.{u} Unit
  let A := fun _ : I => ULift.{v} Base
  let F := ULift.{w} Base
  haveI : IsSimpleGroup F := (MulEquiv.ulift : F ≃* Base).isSimpleGroup
  let B : Subgroup (∀ i : I, A i) := ⊤
  let theta : B →* F := {
    toFun := fun b => ⟨(b.val ⟨()⟩).down⟩
    map_one' := rfl
    map_mul' := fun _ _ => rfl }
  refine ⟨I,inferInstance,A,inferInstance,F,inferInstance,inferInstance,?_,B,?_,theta,?_⟩
  · intro h
    apply base_noncomm
    intro a b
    exact congrArg ULift.down (h ⟨a⟩ ⟨b⟩)
  · intro i a
    exact ⟨⟨fun _ => a, Subgroup.mem_top _⟩,rfl⟩
  · intro a
    exact ⟨⟨fun _ => ⟨a.down⟩, Subgroup.mem_top _⟩,rfl⟩

private theorem rejected_law : ¬ arena.{u,v,w}.Law rejected := by
  intro h
  let p := testData.{u,v,w}
  letI := p.finiteI
  letI := p.groupA
  letI := p.groupF
  letI := p.simpleF
  exact inverse_cannot_factor p
    (h (I := p.I) p.A (F := p.F) p.noncomm p.B p.onto p.theta p.theta_onto)

private theorem dependence : ObservationalDependence signature.{u,v,w} actual := by
  intro i
  let p := testData.{u,v,w}
  letI := p.groupF
  letI := p.simpleF
  obtain ⟨a,b,hab⟩ := exists_pair_ne p.F
  obtain ⟨x,hx⟩ := p.theta_onto a
  obtain ⟨y,hy⟩ := p.theta_onto b
  refine ⟨p,x,y,?_⟩
  change p.theta x ≠ p.theta y
  simpa only [hx,hy] using hab

def family : Registration arena.{u,v,w} statement.{u,v,w} where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @NikolovSegal.subdirect_simple_factorization,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

noncomputable def entry : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@NikolovSegal.subdirect_simple_factorization.{u,v,w})
    (type_of% (realize signature.{u,v,w} (fun _ p b => p.theta b) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `Reg.D5.S3.FiniteGroups.NikolovSegal.SubdirectSimpleFactorization.informationUnit
  realizationName := `Reg.D5.S3.FiniteGroups.NikolovSegal.SubdirectSimpleFactorization.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p b => p.theta b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.FiniteGroups.NikolovSegal.SubdirectSimpleFactorization
    definition := none
    coordinates := #[0,2,4,8,10]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","body","body","body","body","arg","body","arg","body","body","fn","arg"]
      stateBinder := 14
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Reg.D5.S3.FiniteGroups.NikolovSegal.SubdirectSimpleFactorization
