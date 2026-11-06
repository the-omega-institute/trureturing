import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.UniverseSingleReadout
import D5.S3.VertexAlgebra.Analysis.OriginalWeakSmearedLocality
set_option autoImplicit false
noncomputable section
open scoped BigOperators InnerProductSpace Topology ComplexConjugate
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.VertexAlgebra.Analysis.OriginalSmearing
open _root_.D5.S3.VertexAlgebra.Analysis.SmoothCircleFourier
open _root_.D5.S3.VertexAlgebra.LatticeGeneratingFieldLocality
open _root_.D5.S3.VertexAlgebra.LatticePositiveEnergy
open _root_.D5.S3.VertexAlgebra.LatticeAllStateField
open _root_.D5.S3.VertexAlgebra.OriginalGram
namespace Reg.D5.S3.VertexAlgebra.Analysis.OriginalWeakSmearedLocality
private def testLattice : LatticeData where
  rank := 1
  G := Matrix.diagonal (fun _ => 2)
  symmetric := by intro i j; simp [Matrix.diagonal, eq_comm]
  even_diagonal := by intro i; norm_num [Matrix.diagonal]
private theorem test_positive : (gramReal testLattice).PosDef := by
  simpa [gramReal, testLattice] using
    (Matrix.PosDef.diagonal (fun _ : Fin 1 => (by norm_num : (0 : ℝ)<2)))
private def testModel : Model where
  D := testLattice
  positive := test_positive
  inverse := (complex_inverse_exists testLattice test_positive).choose
  inverse_left := (complex_inverse_exists testLattice test_positive).choose_spec.1
  inverse_right := (complex_inverse_exists testLattice test_positive).choose_spec.2
private def zeroTest : Test where
  lift _ := 0
  smooth := contDiff_const
  periodic _ := rfl
private theorem zero_disjoint :
    Disjoint (tsupport zeroTest.periodic.lift) (tsupport zeroTest.periodic.lift) := by
  have hz : zeroTest.periodic.lift = 0 := by
    funext x
    induction x using Quotient.inductionOn with
    | h x => rfl
  simp [hz]
private theorem vacuum_embed_ne : testModel.embed 0 (vacuum testModel.D) ≠ 0 := by
  intro h
  apply vacuum_nonzero testModel.D
  exact UniformSpace.Completion.coe_injective (testModel.Finite 0)
    (h.trans (map_zero (testModel.embed 0)).symm)
structure OpsParams where
  M : Model
  a : Charge M.D
  b : Charge M.D
  k : ℕ
abbrev opsSignature : Signature := _root_.Reg.Support.UniverseSingleReadout.signature
  OpsParams (fun p => p.M.Sobolev (p.M.order p.a+p.M.order p.b+p.k) →L[ℂ] p.M.Sobolev p.k)
    (fun p => (p.M.Sobolev (p.M.order p.a+p.M.order p.b+p.k) →L[ℂ] p.M.Sobolev p.k) → Prop)
def opsActual : Realization opsSignature :=
  realize opsSignature (fun _ _ x y => x=y) (fun e => nomatch e)
def opsRejected : Realization opsSignature :=
  realize opsSignature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem ops_dependence : ObservationalDependence opsSignature opsActual := by
  intro i
  let p : OpsParams := ⟨testModel,0,0,0⟩
  have ho : testModel.order 0+testModel.order 0+0=0 := by simp [Model.order]
  let A : opsSignature.State p :=
    testModel.castSource ho.symm (ContinuousLinearMap.id ℂ testModel.Hilbert)
  have hA : A ≠ 0 := by
    intro h
    have hv := congrArg (fun T : opsSignature.State p =>
      T (testModel.embed (testModel.order 0+testModel.order 0+0) (vacuum testModel.D))) h
    have he : A (testModel.embed (testModel.order 0+testModel.order 0+0)
        (vacuum testModel.D)) = testModel.embed 0 (vacuum testModel.D) := by
      dsimp [A, Model.castSource]
      cases ho
      rfl
    exact vacuum_embed_ne (he.symm.trans (by simpa using hv))
  refine ⟨p,A,0,?_⟩
  intro h
  have hh := congrFun h A
  change (A=A) = ((0 : opsSignature.State p)=A) at hh
  exact hA (Eq.mp hh rfl).symm
abbrev familySignature : Signature := _root_.Reg.Support.UniverseSingleReadout.signature
  Model (fun M => M.Smooth →ₗ[ℂ] M.Smooth) (fun M => (M.Smooth →ₗ[ℂ] M.Smooth) → Prop)
def familyActual : Realization familySignature :=
  realize familySignature (fun _ _ x y => x=y) (fun e => nomatch e)
def familyRejected : Realization familySignature :=
  realize familySignature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem smooth_ne : testModel.finiteFamily (vacuum testModel.D) ≠ 0 := by
  intro h
  apply vacuum_embed_ne
  have he := congrArg (fun x : testModel.Smooth => x.1 0) h
  exact he
private theorem family_dependence : ObservationalDependence familySignature familyActual := by
  intro i
  let A := LinearMap.id (R := ℂ) (M := testModel.Smooth)
  refine ⟨testModel,A,0,?_⟩
  intro h
  have hh := congrFun h A
  have hz : (0 : testModel.Smooth →ₗ[ℂ] testModel.Smooth)=A := Eq.mp hh rfl
  apply smooth_ne
  have he := congrArg (fun T : testModel.Smooth →ₗ[ℂ] testModel.Smooth =>
    T (testModel.finiteFamily (vacuum testModel.D))) hz
  exact he.symm
abbrev fieldSignature : Signature := _root_.Reg.Support.UniverseSingleReadout.signature
  Model (fun M => M.Hilbert) (fun M => M.Hilbert → Prop)
def fieldActual : Realization fieldSignature :=
  realize fieldSignature (fun _ _ x y => x=y) (fun e => nomatch e)
def fieldRejected : Realization fieldSignature :=
  realize fieldSignature (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem field_dependence : ObservationalDependence fieldSignature fieldActual := by
  intro i
  let v := testModel.embed 0 (vacuum testModel.D)
  refine ⟨testModel,v,0,?_⟩
  intro h
  have hh := congrFun h v
  have hz : (0 : testModel.Hilbert)=v := Eq.mp hh rfl
  exact vacuum_embed_ne hz.symm

namespace bounded
def arena : Arena where
  signature := opsSignature
  Law R := ∀ (M : Model) (a b : Charge M.D) (f g : Test),
    Disjoint (tsupport f.periodic.lift) (tsupport g.periodic.lift) → ∀ k : ℕ, R.readout () ⟨M,a,b,k⟩ (M.smearComposition a b f g k)
      (M.reverseSmearComposition a b f g k)
private theorem rejected_bad : ¬ arena.Law opsRejected := by
  intro h
  exact h testModel 0 0 zeroTest zeroTest zero_disjoint 0
def evidence : Registration arena (type_of% (@smearComposition_eq_reverse_of_disjoint_tsupport)) where
  actual := opsActual
  bridge := Iff.rfl
  variation := ⟨@smearComposition_eq_reverse_of_disjoint_tsupport,opsRejected,rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law opsActual opsRejected rejected_bad
  dependence := ops_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@smearComposition_eq_reverse_of_disjoint_tsupport) (Realization opsSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalWeakSmearedLocality.bounded.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalWeakSmearedLocality.bounded.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize opsSignature opsActual.readout opsActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {owner := `D5.S3.VertexAlgebra.Analysis.OriginalWeakSmearedLocality
    definition := none
    coordinates := #[0,1,2,6]
    readouts := #[{path := #["body", "body", "body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]
end bounded

namespace families
def arena : Arena where
  signature := familySignature
  Law R := ∀ (M : Model) (a b : Charge M.D) (f g : Test),
    Disjoint (tsupport f.periodic.lift) (tsupport g.periodic.lift) → R.readout () M ((M.smearFamily a f).comp (M.smearFamily b g))
      ((M.smearFamily b g).comp (M.smearFamily a f))
private theorem rejected_bad : ¬ arena.Law familyRejected := by
  intro h
  exact h testModel 0 0 zeroTest zeroTest zero_disjoint
def evidence : Registration arena (type_of% (@smearFamily_comp_eq_of_disjoint_tsupport)) where
  actual := familyActual
  bridge := Iff.rfl
  variation := ⟨@smearFamily_comp_eq_of_disjoint_tsupport,familyRejected,rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law familyActual familyRejected rejected_bad
  dependence := family_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@smearFamily_comp_eq_of_disjoint_tsupport) (Realization familySignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalWeakSmearedLocality.families.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalWeakSmearedLocality.families.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize familySignature familyActual.readout familyActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {owner := `D5.S3.VertexAlgebra.Analysis.OriginalWeakSmearedLocality
    definition := none
    coordinates := #[0]
    readouts := #[{path := #["body", "body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]
end families

namespace vectors
def arena : Arena where
  signature := fieldSignature
  Law R := ∀ (M : Model) (a b : Charge M.D) (f g : Test),
    Disjoint (tsupport f.periodic.lift) (tsupport g.periodic.lift) → let ha := ((original_smooth_fields M a).choose_spec.2 f).2.2.2.1
    let hb := ((original_smooth_fields M b).choose_spec.2 g).2.2.2.1
    ∀ u : M.smoothDomain, R.readout () M (M.field a f ⟨M.field b g u,hb u⟩)
      (M.field b g ⟨M.field a f u,ha u⟩)
private theorem rejected_bad : ¬ arena.Law fieldRejected := by
  intro h
  exact h testModel 0 0 zeroTest zeroTest zero_disjoint 0
def evidence : Registration arena (type_of% (@field_comp_eq_of_disjoint_tsupport)) where
  actual := fieldActual
  bridge := Iff.rfl
  variation := ⟨@field_comp_eq_of_disjoint_tsupport,fieldRejected,rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law fieldActual fieldRejected rejected_bad
  dependence := field_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@field_comp_eq_of_disjoint_tsupport) (Realization fieldSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalWeakSmearedLocality.vectors.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalWeakSmearedLocality.vectors.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize fieldSignature fieldActual.readout fieldActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {owner := `D5.S3.VertexAlgebra.Analysis.OriginalWeakSmearedLocality
    definition := none
    coordinates := #[0]
    readouts := #[{path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]
end vectors

namespace endpoint
def arena : Arena where
  signature := opsSignature
  Law R := ∀ (M : Model) (a b : Charge M.D) (f g : Test),
    Disjoint (tsupport f.periodic.lift) (tsupport g.periodic.lift) →     (∀ k : ℕ, R.readout () ⟨M,a,b,k⟩ (M.smearComposition a b f g k)
      (M.reverseSmearComposition a b f g k)) ∧
    ((M.smearFamily a f).comp (M.smearFamily b g) =
      (M.smearFamily b g).comp (M.smearFamily a f)) ∧
    (let ha := ((original_smooth_fields M a).choose_spec.2 f).2.2.2.1
     let hb := ((original_smooth_fields M b).choose_spec.2 g).2.2.2.1
     ∀ u : M.smoothDomain,
       (M.field a f ⟨M.field b g u, hb u⟩ =
         M.field b g ⟨M.field a f u, ha u⟩) ∧
       (∀ y : M.Hilbert,
         ⟪y, M.field a f ⟨M.field b g u, hb u⟩⟫_ℂ =
           ⟪y, M.field b g ⟨M.field a f u, ha u⟩⟫_ℂ) ∧
       (∀ v : M.smoothDomain,
         ⟪M.opposite a f v, M.field b g u⟫_ℂ =
           ⟪M.opposite b g v, M.field a f u⟫_ℂ))
private theorem rejected_bad : ¬ arena.Law opsRejected := by
  intro h
  exact (h testModel 0 0 zeroTest zeroTest zero_disjoint).1 0
def evidence : Registration arena (type_of% (@original_smooth_fields_commute)) where
  actual := opsActual
  bridge := Iff.rfl
  variation := ⟨@original_smooth_fields_commute,opsRejected,rejected_bad⟩
  sensitivity := _root_.Reg.Support.UniverseSingleReadout.sensitivity arena.Law opsActual opsRejected rejected_bad
  dependence := ops_dependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@original_smooth_fields_commute) (Realization opsSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalWeakSmearedLocality.endpoint.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.Analysis.OriginalWeakSmearedLocality.endpoint.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := {stage := .evidence, objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize opsSignature opsActual.readout opsActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {owner := `D5.S3.VertexAlgebra.Analysis.OriginalWeakSmearedLocality
    definition := none
    coordinates := #[0,1,2,6]
    readouts := #[{path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "body", "fn", "fn"],
      stateBinder := 0, functionOperand := true, stateOperand := none, booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[]
end endpoint
end Reg.D5.S3.VertexAlgebra.Analysis.OriginalWeakSmearedLocality
