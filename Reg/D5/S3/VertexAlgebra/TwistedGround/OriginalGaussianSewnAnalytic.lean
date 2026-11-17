import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic

noncomputable section
universe u
open scoped BigOperators Topology
open Filter Metric
open _root_.D5.S3.VertexAlgebra
open LatticeGeneratingFieldLocality LatticeHalfFock LatticeHalfFockChargedTensorCoefficients
open TwistedGround
open OriginalGaussianExternalBlocks OriginalGaussianSourceMeans OriginalGaussianDeterminant
open OriginalGaussianMatrix OriginalGaussianSourceGerm OriginalGaussianSewnAnalytic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic

private abbrev hyperbolic : LatticeData where
  rank := 2
  G := !![0, 1; 1, 0]
  symmetric := by intro i j; fin_cases i <;> fin_cases j <;> rfl
  even_diagonal := by intro i; fin_cases i <;> exact ⟨0, rfl⟩
private theorem hyperbolic_unit : IsUnit hyperbolic.G.det := by
  have h : hyperbolic.G.det = -1 := by decide
  rw [h]
  exact isUnit_neg_one
private def labels : Unit → External hyperbolic := fun _ => (false, (0, 0))

abbrev diffSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℂ → ℂ)
    (fun _ => Set ℂ → Prop)
def diffActual : Realization diffSignature :=
  realize _ (fun _ _ f s => DifferentiableOn ℂ f s) (fun e => nomatch e)
def diffBad : Realization diffSignature :=
  realize _ (fun _ _ _ _ => False) (fun e => nomatch e)
private theorem diffDependence : ObservationalDependence diffSignature diffActual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun z => z⁻¹), ?_⟩
  intro h
  have he := congrFun h Set.univ
  have hd : DifferentiableOn ℂ (fun z : ℂ => z⁻¹) Set.univ :=
    Eq.mp he (differentiableOn_const _)
  have hi := differentiableOn_univ.mp hd (0 : ℂ)
  exact (differentiableAt_inv_iff.mp hi) rfl

abbrev uniformSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ → ℂ → ℂ)
    (fun _ => (ℂ → ℂ) → Filter ℕ → Set ℂ → Prop)
def uniformActual : Realization uniformSignature :=
  realize _ (fun _ _ F f l s => TendstoUniformlyOn F f l s) (fun e => nomatch e)
def uniformBad : Realization uniformSignature :=
  realize _ (fun _ _ _ _ _ _ => False) (fun e => nomatch e)
private theorem uniformDependence : ObservationalDependence uniformSignature uniformActual := by
  intro i
  refine ⟨(), (fun _ _ => 0), (fun _ _ => 1), ?_⟩
  intro h
  have he := congrFun (congrFun (congrFun h (fun _ => 0)) atTop) Set.univ
  have hz : TendstoUniformlyOn (fun _ : ℕ => fun _ : ℂ => (0 : ℂ))
      (fun _ => 0) atTop Set.univ := tendsto_const_nhds.tendstoUniformlyOn_const Set.univ
  have hp := (Eq.mp he hz).tendsto_at (Set.mem_univ (0 : ℂ))
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hp)

abbrev localSignature : Signature := uniformSignature
def localActual : Realization localSignature :=
  realize _ (fun _ _ F f l s => TendstoLocallyUniformlyOn F f l s) (fun e => nomatch e)
def localBad : Realization localSignature :=
  realize _ (fun _ _ _ _ _ _ => False) (fun e => nomatch e)
private theorem localDependence : ObservationalDependence localSignature localActual := by
  intro i
  refine ⟨(), (fun _ _ => 0), (fun _ _ => 1), ?_⟩
  intro h
  have he := congrFun (congrFun (congrFun h (fun _ => 0)) atTop) Set.univ
  have hz : TendstoLocallyUniformlyOn (fun _ : ℕ => fun _ : ℂ => (0 : ℂ))
      (fun _ => 0) atTop Set.univ :=
    (tendsto_const_nhds.tendstoUniformlyOn_const Set.univ).tendstoLocallyUniformlyOn
  have hp := (Eq.mp he hz).tendsto_at (Set.mem_univ (0 : ℂ))
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hp)

abbrev coefficientSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ → ℂ)
    (fun _ => Filter ℕ → Filter ℂ → Prop)
def coefficientActual : Realization coefficientSignature :=
  realize _ (fun _ _ F l g => Tendsto F l g) (fun e => nomatch e)
def coefficientBad : Realization coefficientSignature :=
  realize _ (fun _ _ _ _ _ => False) (fun e => nomatch e)
private theorem coefficientDependence : ObservationalDependence coefficientSignature coefficientActual := by
  intro i
  refine ⟨(), (fun _ => 0), (fun _ => 1), ?_⟩
  intro h
  have he := congrFun (congrFun h atTop) (𝓝 (0 : ℂ))
  have hp : Tendsto (fun _ : ℕ => (1 : ℂ)) atTop (𝓝 0) := Eq.mp he tendsto_const_nhds
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds hp)

namespace finiteSewn_differentiableOn
def arena : Arena where
  signature := diffSignature
  Law A := ∀ {X : Type u} [Fintype X] [DecidableEq X] (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D) (e : X → External D) (d : (X ⊕ X) →₀ ℕ) (N : ℕ),
    A.readout () () (finiteSewn D a e d N) (ball (0 : ℂ) 1)
private theorem bad_fails : ¬ arena.{u}.Law diffBad := by
  intro h
  exact @h (ULift.{u} Unit) inferInstance inferInstance hyperbolic hyperbolic_unit 0 (fun _ => labels ()) 0 0
def evidence : Registration arena.{u} (type_of% (@finiteSewn_differentiableOn.{u})) where
  actual := diffActual
  bridge := Iff.rfl
  variation := ⟨fun {X} _ _ D hu a e d N => finiteSewn_differentiableOn D hu a e d N, diffBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law diffActual diffBad bad_fails
  dependence := diffDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finiteSewn_differentiableOn.{u}) (Realization diffSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic.finiteSewn_differentiableOn.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic.finiteSewn_differentiableOn.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize diffSignature diffActual.readout diffActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end finiteSewn_differentiableOn

namespace sewn_differentiableOn
def arena : Arena where
  signature := diffSignature
  Law A := ∀ {X : Type u} [Fintype X] [DecidableEq X] (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D) (e : X → External D) (d : (X ⊕ X) →₀ ℕ),
    A.readout () () (sewn D a e d) (ball (0 : ℂ) 1)
private theorem bad_fails : ¬ arena.{u}.Law diffBad := by
  intro h
  exact @h (ULift.{u} Unit) inferInstance inferInstance hyperbolic hyperbolic_unit 0 (fun _ => labels ()) 0
def evidence : Registration arena.{u} (type_of% (@sewn_differentiableOn.{u})) where
  actual := diffActual
  bridge := Iff.rfl
  variation := ⟨fun {X} _ _ D hu a e d => sewn_differentiableOn D hu a e d, diffBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law diffActual diffBad bad_fails
  dependence := diffDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sewn_differentiableOn.{u}) (Realization diffSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic.sewn_differentiableOn.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic.sewn_differentiableOn.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize diffSignature diffActual.readout diffActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end sewn_differentiableOn

namespace finiteSewn_tendstoUniformlyOn
def arena : Arena where
  signature := uniformSignature
  Law A := ∀ {X : Type u} [Fintype X] [DecidableEq X] (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D) (e : X → External D) (d : (X ⊕ X) →₀ ℕ) (ρ : ℝ), 0 ≤ ρ → ρ < 1 →
    A.readout () () (finiteSewn D a e d) (sewn D a e d) atTop {z : ℂ | ‖z‖ ≤ ρ}
private theorem bad_fails : ¬ arena.{u}.Law uniformBad := by
  intro h
  exact @h (ULift.{u} Unit) inferInstance inferInstance hyperbolic hyperbolic_unit 0 (fun _ => labels ()) 0 0 le_rfl (by norm_num)
def evidence : Registration arena.{u} (type_of% (@finiteSewn_tendstoUniformlyOn.{u})) where
  actual := uniformActual
  bridge := Iff.rfl
  variation := ⟨fun {X} _ _ D hu a e d ρ hρ hρ1 => finiteSewn_tendstoUniformlyOn D hu a e d hρ hρ1, uniformBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law uniformActual uniformBad bad_fails
  dependence := uniformDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finiteSewn_tendstoUniformlyOn.{u}) (Realization uniformSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic.finiteSewn_tendstoUniformlyOn.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic.finiteSewn_tendstoUniformlyOn.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize uniformSignature uniformActual.readout uniformActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end finiteSewn_tendstoUniformlyOn

namespace finiteSewn_tendstoLocallyUniformlyOn
def arena : Arena where
  signature := localSignature
  Law A := ∀ {X : Type u} [Fintype X] [DecidableEq X] (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D) (e : X → External D) (d : (X ⊕ X) →₀ ℕ),
    A.readout () () (finiteSewn D a e d) (sewn D a e d) atTop (ball (0 : ℂ) 1)
private theorem bad_fails : ¬ arena.{u}.Law localBad := by
  intro h
  exact @h (ULift.{u} Unit) inferInstance inferInstance hyperbolic hyperbolic_unit 0 (fun _ => labels ()) 0
def evidence : Registration arena.{u} (type_of% (@finiteSewn_tendstoLocallyUniformlyOn.{u})) where
  actual := localActual
  bridge := Iff.rfl
  variation := ⟨fun {X} _ _ D hu a e d => finiteSewn_tendstoLocallyUniformlyOn D hu a e d, localBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law localActual localBad bad_fails
  dependence := localDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finiteSewn_tendstoLocallyUniformlyOn.{u}) (Realization localSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic.finiteSewn_tendstoLocallyUniformlyOn.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic.finiteSewn_tendstoLocallyUniformlyOn.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize localSignature localActual.readout localActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end finiteSewn_tendstoLocallyUniformlyOn

namespace finiteSewn_coefficient_tendsto
def arena : Arena where
  signature := coefficientSignature
  Law A := ∀ {X : Type u} [Fintype X] [DecidableEq X] (D : LatticeData) (hu : IsUnit D.G.det) (a : Charge D) (e : X → External D) (d : (X ⊕ X) →₀ ℕ) (m : ℕ),
    A.readout () () (fun N => coefficient m (finiteSewn D a e d N))
      atTop (𝓝 (coefficient m (sewn D a e d)))
private theorem bad_fails : ¬ arena.{u}.Law coefficientBad := by
  intro h
  exact @h (ULift.{u} Unit) inferInstance inferInstance hyperbolic hyperbolic_unit 0 (fun _ => labels ()) 0 0
def evidence : Registration arena.{u} (type_of% (@finiteSewn_coefficient_tendsto.{u})) where
  actual := coefficientActual
  bridge := Iff.rfl
  variation := ⟨fun {X} _ _ D hu a e d m => finiteSewn_coefficient_tendsto D hu a e d m, coefficientBad, bad_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.{u}.Law coefficientActual coefficientBad bad_fails
  dependence := coefficientDependence
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@finiteSewn_coefficient_tendsto.{u}) (Realization coefficientSignature) Type Unit where
  unitName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic.finiteSewn_coefficient_tendsto.unit
  realizationName := `Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic.finiteSewn_coefficient_tendsto.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coefficientSignature coefficientActual.readout coefficientActual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end finiteSewn_coefficient_tendsto

end Reg.D5.S3.VertexAlgebra.TwistedGround.OriginalGaussianSewnAnalytic
