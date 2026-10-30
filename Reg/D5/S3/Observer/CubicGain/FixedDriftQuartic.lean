import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Observer.CubicGain.FixedDriftQuartic
import Reg.Support.SingleDependentReadout

/-! The full parent predicate, varied on the unrestricted original-world carrier. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace Reg.D5.S3.Observer.CubicGain.FixedDriftQuartic
open _root_.D5.S3.Observer.CubicGain
open _root_.D5.S3.Observer.CubicGain.FixedDriftQuartic
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => OriginalWorld) (fun _ => Prop)

def actual : Realization signature :=
  realize signature (fun _ _ => OriginalParent) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => True) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (d p v : ℝ), d ≠ 0 → d ≠ 24 →
    let parents : Set OriginalWorld :=
      {W | R.readout () () W ∧ W.2.2.1=d ∧ (originalPolynomial W).eval 7=0}
    let children : Set OriginalWorld :=
      {W | W ∈ parents ∧ originalRead W 5=p ∧ originalRead W 6=v}
    (∃ e : S d p v ≃ children,
      (∀ u, (e u).1 = reconstruct d u.1) ∧
      (∀ W, (e.symm W).1 = coordinate W.1) ∧
      (∀ u : S d p v,
        originalPolynomial (e u).1 = gPoly d u.1 ∧
        sourceJ (e u).1.1 (e u).1.2.1 = j d u.1 ∧
        sourceN (e u).1.1 (e u).1.2.1 = n d u.1)) ∧
    parents.Finite ∧ parents.ncard ≤ 10 ∧ children.Finite ∧ children.ncard ≤ 4

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hfin := (h 1 0 0 (by norm_num) (by norm_num)).2.1
  let f : ℝ → OriginalWorld := fun x => (x,0,1,0)
  have hinj : Function.Injective f := by
    intro x y he
    exact congrArg Prod.fst he
  have hrange : Set.range f ⊆
      {W : OriginalWorld | rejected.readout () () W ∧ W.2.2.1=1 ∧
        (originalPolynomial W).eval 7=0} := by
    rintro _ ⟨x,rfl⟩
    simp [f,rejected,realize,originalPolynomial,Polynomial.ofFn_zero]
  exact (Set.infinite_range_of_injective hinj).not_finite (hfin.subset hrange)

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  let good := encodeWorld (parentWorld (1/2,1/8,0))
  let bad : OriginalWorld := (0,0,0,0)
  have hg : OriginalParent good := encoded_parent _
    ⟨by norm_num,by norm_num,by norm_num,by norm_num [parentEq]⟩
  refine ⟨(),good,bad,?_⟩
  intro he
  have hb : OriginalParent bad := Eq.mp he hg
  norm_num [OriginalParent,bad] at hb

def source_registration : Registration arena (type_of% @fixed_drift_classification) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨fixed_drift_classification,rejected,rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected
    rejected_law
  dependence := dependence

def registration :
    LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@fixed_drift_classification) (Realization signature) Unit Unit := {
  unitName := `D5.S3.Observer.CubicGain.FixedDriftQuartic.fixed_drift_classification.__information_unit
  realizationName := `Reg.D5.S3.Observer.CubicGain.FixedDriftQuartic.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ => OriginalParent) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Observer.CubicGain.FixedDriftQuartic
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body","body","body","body","body","value","arg","body","fn","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms source_registration
#print axioms registration
end Reg.D5.S3.Observer.CubicGain.FixedDriftQuartic
