import D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

noncomputable section
open LeanInformationAudit
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport
open D5.S3.ConceptDynamics.PartialIdentification.EnabledPathSwapConnectivity
namespace Reg.D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport
universe u v
abbrev signature : Signature where
  Params := Type v
  State p := p
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{v} := realize signature (fun _ _ x y => x = y) (fun e => nomatch e)
def rejected : Realization signature.{v} := realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

def auditedPaths (r : Realization signature.{v}) {E : Type u} [PartialOrder E]
    (R : DependentReadout.{u,v} E) : Prop :=
  ∀ {I J : Set E}, IsLowerSet I → IsLowerSet J → J.Finite →
    ∀ (l m : List E) (hl : Exec I l J) (hm : Exec I m J) (x : R.fibre I),
      r.readout () (R.fibre J) (pathMap R l hl x) (pathMap R m hm x)

def auditedDiamonds (r : Realization signature.{v}) {E : Type u} [PartialOrder E]
    (R : DependentReadout.{u,v} E) : Prop :=
  ∀ {K : Set E} {a b : E}, IsLowerSet K → K.Finite →
    ∀ (ha : Enabled K a) (hb : Enabled K b)
      (hab : Enabled (insert a K) b) (hba : Enabled (insert b K) a) (x : R.fibre K),
      r.readout () (R.fibre (insert b (insert a K)))
        (pathMap R [a,b] ⟨ha,hab,rfl⟩ x)
        (pathMap R [b,a] ⟨hb,hba,Set.insert_comm a b K⟩ x)

abbrev arena : Arena where
  signature := signature.{v}
  Law r := ∀ {E : Type u} [PartialOrder E] (R : DependentReadout.{u,v} E),
    auditedPaths r R ↔ auditedDiamonds r R

private theorem rejected_law : ¬ arena.{u,v}.Law rejected := by
  intro h
  let R : DependentReadout (ULift.{u} Unit) := {
    fibre := fun _ => ULift.{v} Unit
    edge := fun _ x => x }
  have hd : auditedDiamonds rejected R := by
    intro K a b hK hf ha hb hab hba x
    have he : b = a := Subsingleton.elim _ _
    subst b
    exact (hab.1 (Set.mem_insert a K)).elim
  exact (h R).mpr hd (I := ∅) (J := ∅) (by simp [IsLowerSet])
    (by simp [IsLowerSet]) Set.finite_empty [] [] rfl rfl (ULift.up ())

private theorem dependence : ObservationalDependence signature.{v} actual := by
  intro i
  refine ⟨ULift.{v} Bool,ULift.up false,ULift.up true,?_⟩
  intro h
  have hh : (ULift.up false : ULift.{v} Bool) = ULift.up true := (congrFun h (ULift.up true)).mpr rfl
  have hh' := congrArg ULift.down hh
  cases hh'

def family : Registration arena.{u,v} (type_of% (@pathIndependent_iff_diamondCompatible.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pathIndependent_iff_diamondCompatible,rejected,rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rejected_law⟩,fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@pathIndependent_iff_diamondCompatible.{u,v})
    (type_of% (realize signature.{v} (fun _ _ x y => x = y) (fun e => nomatch e))) Unit Unit := {
  unitName := `D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport.pathIndependent_iff_diamondCompatible.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport
    definition := none
    coordinates := #[0,1,2]
    readouts := #[{
      path := #["body","body","body","arg","fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms family


abbrev predicateSignature : Signature where
  Params := Σ X : Type u, X → Prop
  State p := p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def predicateActual : Realization predicateSignature.{u} :=
  realize predicateSignature (fun _ p x => p.2 x) (fun e => nomatch e)
def predicateRejected : Realization predicateSignature.{u} :=
  realize predicateSignature (fun _ _ _ => False) (fun e => nomatch e)

private theorem predicateDependence : ObservationalDependence predicateSignature.{u} predicateActual := by
  intro i
  refine ⟨⟨ULift.{u} Bool,fun x => x.down = true⟩,ULift.up false,ULift.up true,?_⟩
  simp [predicateActual,realize]

abbrev executionArena : Arena where
  signature := predicateSignature.{u}
  Law r := ∀ {E : Type u} [PartialOrder E] {I J : Set E},
    IsLowerSet I → IsLowerSet J → J.Finite →
    ((∃ l, Exec I l J) ↔ r.readout () ⟨Set E,fun K => K ⊆ J⟩ I)

private theorem executionRejected : ¬ executionArena.{u}.Law predicateRejected := by
  intro h
  have hh := h (E := ULift.{u} Unit) (I := ∅) (J := ∅)
    (by simp [IsLowerSet]) (by simp [IsLowerSet]) Set.finite_empty
  exact hh.mp ⟨[],rfl⟩

abbrev appendArena : Arena where
  signature := predicateSignature.{u}
  Law r := ∀ {E : Type u} [PartialOrder E] {I K J : Set E} {p s : List E},
    Exec I p K → Exec K s J → r.readout () ⟨List E,fun l => Exec I l J⟩ (p ++ s)

private theorem appendRejected : ¬ appendArena.{u}.Law predicateRejected := by
  intro h
  exact h (E := ULift.{u} Unit) (I := ∅) (K := ∅) (J := ∅) (p := []) (s := []) rfl rfl

abbrev clocksArena : Arena where
  signature := predicateSignature.{u}
  Law r := ∀ {E : Type u} [PartialOrder E] (C D B : Finset E),
    IsLowerSet (C : Set E) → IsLowerSet (D : Set E) →
    C ⊆ D → D ⊆ B → ∀ (observed : E → Prop) (weight : E → ℝ),
    (∀ e, observed e → 0 < weight e) →
    ∃ l : List E, Exec (C : Set E) l D ∧ l.length = gapCard C D ∧
      (∀ m : List E, Exec (C : Set E) m D → m.length = gapCard C D) ∧
      gapCard C B = gapCard C D + gapCard D B ∧
      r.readout () ⟨Finset E,fun K => clockFinite observed weight K ≤ clockFinite observed weight D⟩ C ∧
      ((∃ e ∈ D, e ∉ C ∧ observed e) →
        clockFinite observed weight C < clockFinite observed weight D) ∧
      (∀ m : List E, Exec (D : Set E) m C → l = []) ∧
      (∀ e pieces tail, pathWeight weight (e :: tail) = pathWeight weight (pieces ++ tail) ↔
        weight e = pathWeight weight pieces)

private theorem clocksRejected : ¬ clocksArena.{u}.Law predicateRejected := by
  intro h
  obtain ⟨l,hl,hlen,hall,hgap,hclock,_⟩ := h (E := ULift.{u} Unit) ∅ ∅ ∅
    (by simp [IsLowerSet]) (by simp [IsLowerSet]) (by simp) (by simp)
    (fun _ => False) (fun _ => 0) (by simp)
  exact hclock

abbrev pathAppendArena : Arena where
  signature := signature.{v}
  Law r := ∀ {E : Type u} [PartialOrder E] (R : DependentReadout.{u,v} E)
    {I K J : Set E} {p s : List E} (hp : Exec I p K) (hs : Exec K s J) (x : R.fibre I),
    r.readout () (R.fibre J) (pathMap R (p ++ s) (exec_append hp hs) x)
      (pathMap R s hs (pathMap R p hp x))

private theorem pathAppendRejected : ¬ pathAppendArena.{u,v}.Law rejected := by
  intro h
  let R : DependentReadout (ULift.{u} Unit) := {
    fibre := fun _ => ULift.{v} Unit
    edge := fun _ x => x }
  exact h R (I := ∅) (K := ∅) (J := ∅) (p := []) (s := []) rfl rfl (ULift.up ())

abbrev rootArena : Arena where
  signature := signature.{v}
  Law q := ∀ {V : Type u} {G : BiGraph V} {F : V → Type v}
    (T : EdgeTransport G F) (r : V) (hc : GraphConnectedFrom G r),
    (∀ {x y : RootFixedPoint T r}, rootSectionMap T r hc x = rootSectionMap T r hc y →
      q.readout () (RootFixedPoint T r) x y) ∧ Function.Surjective (rootSectionMap T r hc)

private theorem rootRejected : ¬ rootArena.{u,v}.Law rejected := by
  intro h
  let V := ULift.{u} Unit
  let G : BiGraph V := ⟨fun _ _ => False,fun h => h⟩
  let F : V → Type v := fun _ => ULift.{v} Unit
  let T : EdgeTransport G F := EdgeTransport.ofEdges (fun h => False.elim h) (fun h => False.elim h)
  let r : V := ULift.up ()
  have hc : GraphConnectedFrom G r := by
    intro v
    have hv : v = r := Subsingleton.elim _ _
    subst v
    exact ⟨.nil r⟩
  have hx : RootFixed T r (ULift.up ()) := by
    intro q
    cases q with
    | nil => rfl
    | cons he => exact False.elim he
  let x : RootFixedPoint T r := ⟨ULift.up (),hx⟩
  exact (h T r hc).1 (x := x) (y := x) rfl

abbrev treeArena : Arena where
  signature := predicateSignature.{max u v}
  Law q := ∀ {V : Type u} {G : SimpleGraph V} {F : V → Type v}, G.IsTree →
    ∀ (r : V) (edge : ∀ {v w}, G.Adj v w → F v ≃ F w),
    (∀ {v w} (h : G.Adj v w), edge h.symm = (edge h).symm) →
    ∃ coordinates : ∀ v, F r ≃ F v,
      q.readout () ⟨(∀ v, F r ≃ F v),fun c => ∀ {v w} (h : G.Adj v w),
        ((c v).trans (edge h)).trans (c w).symm = Equiv.refl (F r)⟩ coordinates

private theorem treeRejected : ¬ treeArena.{u,v}.Law predicateRejected := by
  intro h
  let G : SimpleGraph (ULift.{u} Unit) := ⊥
  let F : ULift.{u} Unit → Type v := fun _ => ULift.{v} Unit
  obtain ⟨c,hc⟩ := h (G := G) (F := F) SimpleGraph.IsTree.of_subsingleton (ULift.up ())
    (fun he => False.elim he) (fun he => False.elim he)
  exact hc

def executionFamily : Registration executionArena.{u} (type_of% (@exec_exists_iff_subset.{u})) where
  actual := predicateActual
  bridge := Iff.rfl
  variation := ⟨@exec_exists_iff_subset,predicateRejected,executionRejected⟩
  sensitivity := ⟨fun i => ⟨predicateRejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,executionRejected⟩,fun e => nomatch e⟩
  dependence := predicateDependence

def executionRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exec_exists_iff_subset.{u})
    (type_of% (predicateActual.{u})) Unit Unit := {
  unitName := `D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport.exec_exists_iff_subset.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport.executionFamily
  realizationSource := none
  generated := false
  arena := .source ⟨executionArena⟩
  objectArena := .source ⟨executionArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source executionArena ⟨executionFamily⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize predicateSignature (fun _ p x => p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms executionFamily

def appendFamily : Registration appendArena.{u} (type_of% (@exec_append.{u})) where
  actual := predicateActual
  bridge := Iff.rfl
  variation := ⟨@exec_append,predicateRejected,appendRejected⟩
  sensitivity := ⟨fun i => ⟨predicateRejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,appendRejected⟩,fun e => nomatch e⟩
  dependence := predicateDependence

def appendRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exec_append.{u})
    (type_of% (predicateActual.{u})) Unit Unit := {
  unitName := `D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport.exec_append.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport.appendFamily
  realizationSource := none
  generated := false
  arena := .source ⟨appendArena⟩
  objectArena := .source ⟨appendArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source appendArena ⟨appendFamily⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize predicateSignature (fun _ p x => p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms appendFamily

def clocksFamily : Registration clocksArena.{u} (type_of% (@finite_history_clocks.{u})) where
  actual := predicateActual
  bridge := Iff.rfl
  variation := ⟨@finite_history_clocks,predicateRejected,clocksRejected⟩
  sensitivity := ⟨fun i => ⟨predicateRejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,clocksRejected⟩,fun e => nomatch e⟩
  dependence := predicateDependence

def clocksRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@finite_history_clocks.{u})
    (type_of% (predicateActual.{u})) Unit Unit := {
  unitName := `D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport.finite_history_clocks.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport.clocksFamily
  realizationSource := none
  generated := false
  arena := .source ⟨clocksArena⟩
  objectArena := .source ⟨clocksArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source clocksArena ⟨clocksFamily⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize predicateSignature (fun _ p x => p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms clocksFamily

def pathAppendFamily : Registration pathAppendArena.{u,v} (type_of% (@pathMap_append.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@pathMap_append,rejected,pathAppendRejected⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,pathAppendRejected⟩,fun e => nomatch e⟩
  dependence := dependence

def pathAppendRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@pathMap_append.{u,v})
    (type_of% (actual.{v})) Unit Unit := {
  unitName := `D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport.pathMap_append.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport.pathAppendFamily
  realizationSource := none
  generated := false
  arena := .source ⟨pathAppendArena⟩
  objectArena := .source ⟨pathAppendArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pathAppendArena ⟨pathAppendFamily⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms pathAppendFamily

def rootFamily : Registration rootArena.{u,v} (type_of% (@rootSectionMap_bijective.{u,v})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@rootSectionMap_bijective,rejected,rootRejected⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,rootRejected⟩,fun e => nomatch e⟩
  dependence := dependence

def rootRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@rootSectionMap_bijective.{u,v})
    (type_of% (actual.{v})) Unit Unit := {
  unitName := `D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport.rootSectionMap_bijective.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport.rootFamily
  realizationSource := none
  generated := false
  arena := .source ⟨rootArena⟩
  objectArena := .source ⟨rootArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rootArena ⟨rootFamily⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms rootFamily

def treeFamily : Registration treeArena.{u,v} (type_of% (@tree_coordinate_trivialization.{u,v})) where
  actual := predicateActual
  bridge := Iff.rfl
  variation := ⟨@tree_coordinate_trivialization,predicateRejected,treeRejected⟩
  sensitivity := ⟨fun i => ⟨predicateRejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim,rfl,treeRejected⟩,fun e => nomatch e⟩
  dependence := predicateDependence

def treeRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@tree_coordinate_trivialization.{u,v})
    (type_of% (predicateActual.{max u v})) Unit Unit := {
  unitName := `D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport.tree_coordinate_trivialization.__information_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport.treeFamily
  realizationSource := none
  generated := false
  arena := .source ⟨treeArena⟩
  objectArena := .source ⟨treeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source treeArena ⟨treeFamily⟩
  correspondence := {stage := .evidence,objectStage := .evidence}
  bundleNonempty := .absent
  readout := some (realize predicateSignature (fun _ p x => p.2 x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport
    definition := none
    coordinates := #[0,1]
    readouts := #[{
      path := #["body","body","body","body"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false}]}
  continuation := .unknown
  familyRecord := none
  options := #[] }
#print axioms treeFamily
end Reg.D5.S3.ConceptDynamics.Fibers.ConfigurationPathTransport
