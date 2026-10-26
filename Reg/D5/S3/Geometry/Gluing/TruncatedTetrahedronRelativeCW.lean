import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Geometry.Gluing.TruncatedTetrahedronRelativeCW
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)
open _root_.D5.S3.Geometry.Gluing.ActualLinkAffineFan (TruncatedPoint)
open _root_.D5.S3.Geometry.Gluing.TruncatedTetrahedronRelativeCW

namespace Reg.D5.S3.Geometry.Gluing.TruncatedTetrahedronRelativeCW
noncomputable section
universe u

/-- Independent carrier and pairing coordinates. The law below retains every
finite and topological dictionary in the original theorem telescope. -/
structure PairingData where
  T : Type u
  pairing : RawFacePairing T

abbrev signature : Signature where
  Params := PairingData.{u}
  State p := TruncatedPoint p.T
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := TruncatedQuotient p.pairing
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p => q p.pairing) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ (p : PairingData.{u}) (finiteT : Fintype p.T)
    (topologyT : TopologicalSpace p.T) (discreteT : @DiscreteTopology p.T topologyT),
    @UpperGeometry p.T finiteT topologyT discreteT p.pairing (R.readout () p)

theorem bridge : (type_of% (@upper_geometry.{u})) ↔ arena.{u}.Law actual := by
  constructor
  · intro h p finiteT topologyT discreteT
    exact @h p.T finiteT topologyT discreteT p.pairing
  · intro h T finiteT topologyT discreteT P
    exact h ⟨T,P⟩ finiteT topologyT discreteT

/-- A whole-family intervention that erases every coordinate within each tag. -/
def barycenter (p : PairingData.{u}) (a : TruncatedPoint p.T) : TruncatedPoint p.T :=
  (a.1, ⟨fun _ => 1/4, by
    constructor
    · intro i
      norm_num
    · norm_num [Fin.sum_univ_succ]⟩)

def rejected : Realization signature.{u} :=
  realize signature (fun _ p a => q p.pairing (barycenter p a)) (fun e => nomatch e)

private def flipFace : Equiv.Perm (Fin 4) :=
  (Equiv.swap 0 1).trans (Equiv.swap 2 3)

private def testPairing : RawFacePairing (ULift.{u} Unit) where
  facePair := Equiv.prodCongr (Equiv.refl _) flipFace
  faceMap _ := Equiv.refl _
  pairInvolutive := by
    apply Equiv.ext
    rintro ⟨t,f⟩
    apply Prod.ext
    · rfl
    · change flipFace (flipFace f) = f
      fin_cases f <;> decide
  pairFixedFree := by
    rintro ⟨t,f⟩ he
    have hf : flipFace f = f := congrArg Prod.snd he
    have hnf : flipFace f ≠ f := by
      fin_cases f <;> decide
    exact hnf hf
  mapInverse _ _ := rfl

private abbrev test : PairingData.{u} :=
  ⟨ULift.{u} Unit,testPairing⟩

private def a : TruncatedPoint test.T :=
  (⟨()⟩, ⟨fun _ => 1/4, by
    constructor
    · intro i
      norm_num
    · norm_num [Fin.sum_univ_succ]⟩)

private def b : TruncatedPoint test.T :=
  (⟨()⟩, ⟨![1/8,3/8,1/4,1/4], by
    constructor
    · intro i
      fin_cases i <;> norm_num
    · norm_num [Fin.sum_univ_succ]⟩)

private theorem a_interior : Interior (a.{u}) := by
  intro i
  norm_num [a]

private theorem b_ne_a : b.{u} ≠ a := by
  intro h
  have hc := congrArg (fun z : TruncatedPoint test.T => z.2.val 0) h
  norm_num [a,b] at hc

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have he : rejected.readout () test a = rejected.readout () test b := by
    apply congrArg (q test.pairing)
    rfl
  exact b_ne_a ((h test inferInstance inferInstance inferInstance).interior_fibers a b a_interior |>.mp he)

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨test,a,b,?_⟩
  intro h
  exact b_ne_a ((upper_geometry test.pairing).interior_fibers a b a_interior |>.mp h)

def familyRegistration : Registration arena.{u} (type_of% (@upper_geometry.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp @upper_geometry,rejected,rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected,?_,rfl,rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := dependence

/-- The geometric source law observed through the original quotient projection. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@upper_geometry.{u})
    (type_of% (realize signature.{u} (fun _ p => q p.pairing) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S3.Geometry.Gluing.TruncatedTetrahedronRelativeCW.upper_geometry.information_unit,
  realizationName := `Reg.D5.S3.Geometry.Gluing.TruncatedTetrahedronRelativeCW.familyRegistration,
  realizationSource := none,
  generated := false,
  arena := .source ⟨arena.{u}⟩,
  objectArena := .source ⟨arena.{u}⟩,
  catalog := Lean.Name.anonymous,
  localNames := false,
  realization := .source arena.{u} ⟨familyRegistration⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature.{u} (fun _ p => q p.pairing) (fun e => nomatch e)),
  variation := .absent,
  sensitivity := .absent,
  partialSensitivity := none,
  escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.Geometry.Gluing.TruncatedTetrahedronRelativeCW,
    definition := none,
    coordinates := #[0,4],
    readouts := #[{
      path := #["body","body","body","body","body","arg"],
      stateBinder := 0,
      functionOperand := true,
      stateOperand := none,
      booleanPredicate := false }] },
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true },
    { name := `internal.cmdlineSnapshots, value := .bool true },
    { name := `linter.mathlibStandardSet, value := .bool true },
    { name := `maxSynthPendingDepth, value := .nat 3 },
    { name := `pp.unicode.fun, value := .bool true },
    { name := `relaxedAutoImplicit, value := .bool false }] }

end

end Reg.D5.S3.Geometry.Gluing.TruncatedTetrahedronRelativeCW
