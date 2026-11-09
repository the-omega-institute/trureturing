import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteElementaryCollapse

/-! Source-bound observations of the original free-pair faces and coordinate deformation. -/

noncomputable section
open Set Finset Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry.FiniteElementaryCollapse
open _root_.D5.S3.Geometry.FiniteConeCollapse
open _root_.D5.S3.Geometry.FiniteSimplicialJoin

namespace Reg.D5.S3.Geometry.FiniteElementaryCollapse
universe u

structure Parameters where
  V : Type u
  finiteVertices : Fintype V
  decidableVertices : DecidableEq V
attribute [instance] Parameters.finiteVertices Parameters.decidableVertices

/-- A simplex with one facet designated as lower face; every original label remains. -/
def simplexPair {V : Type u} [Fintype V] [DecidableEq V] (a : V)
    (h : (Finset.univ.erase a).Nonempty) : CollapsePair V where
  ambient := ⊤
  lower := Finset.univ.erase a
  apex := a
  lower_nonempty := h
  apex_notMem := Finset.notMem_erase _ _
  upper_mem := Finset.insert_nonempty _ _
  free := by
    intro s hs hlt
    have ha : a ∈ s := by
      by_contra hn
      have he : s = Finset.univ.erase a :=
        Finset.Subset.antisymm (fun v hv => Finset.mem_erase.mpr ⟨fun he => hn (he ▸ hv),
          Finset.mem_univ _⟩) hlt.subset
      exact hlt.ne he.symm
    rw [Finset.insert_erase (Finset.mem_univ a)]
    exact Finset.eq_univ_of_forall (fun v => by
      by_cases hv : v = a
      · simpa [hv] using ha
      · exact hlt.subset (Finset.mem_erase.mpr ⟨hv, Finset.mem_univ _⟩))

abbrev sampleParameters : Parameters.{u} := ⟨ULift.{u} (Fin 3), inferInstance, inferInstance⟩
def samplePair (a : Fin 3) : CollapsePair sampleParameters.{u}.V :=
  simplexPair (ULift.up a) (by
    have hn : ∃ b : Fin 3, b ≠ a := exists_ne a
    obtain ⟨b, hb⟩ := hn
    exact ⟨ULift.up b, Finset.mem_erase.mpr ⟨fun he => hb (congrArg ULift.down he),
      Finset.mem_univ _⟩⟩)

structure PairParameters extends Parameters.{u} where
  pair : CollapsePair V

/-- The apex singleton is retained for every free pair, with no inhabitedness assumption. -/
theorem apex_face (p : PairParameters.{u}) : ({p.pair.apex} : Finset p.V) ∈ p.pair.retained := by
  refine ⟨(p.pair.ambient.isRelLowerSet_faces p.pair.upper_mem).2
    (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
    (Finset.singleton_nonempty _), ?_⟩
  intro h
  obtain ⟨v, hv⟩ := p.pair.lower_nonempty
  exact p.pair.apex_notMem ((Finset.mem_singleton.mp (h hv)) ▸ hv)

abbrev sample : PairParameters.{u} := ⟨sampleParameters, samplePair 0⟩

abbrev faceSignature : Signature where
  Params := Type u
  State V := PreAbstractSimplicialComplex V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ V := Finset V → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def faceActual : Realization faceSignature.{u} :=
  realize faceSignature (fun _ _ K s => s ∈ K) (fun e => nomatch e)
def faceRejected : Realization faceSignature.{u} :=
  realize faceSignature (fun _ _ _ _ => False) (fun e => nomatch e)
def faceAlways : Realization faceSignature.{u} :=
  realize faceSignature (fun _ _ _ _ => True) (fun e => nomatch e)
private theorem faceDependence : ObservationalDependence faceSignature.{u} faceActual := by
  intro i
  refine ⟨ULift.{u} Unit, ⊥, ⊤, ?_⟩
  intro h
  have hh := congrFun h ({ULift.up ()} : Finset (ULift.{u} Unit))
  change False = ({ULift.up ()} : Finset (ULift.{u} Unit)).Nonempty at hh
  exact Eq.mpr hh (Finset.singleton_nonempty _)

namespace Lower
abbrev arena : Arena where
  signature := faceSignature.{u}
  Law R := ∀ {V : Type u} [fv : Fintype V] [dv : DecidableEq V] (P : CollapsePair V),
    R.readout () V P.ambient P.lower
private theorem bridge : (type_of% (@CollapsePair.lower_mem.{u})) ↔ arena.{u}.Law faceActual := Iff.rfl
private theorem negative : ¬ arena.{u}.Law faceRejected := by
  intro h
  exact @h sampleParameters.V inferInstance inferInstance (samplePair 0)
end Lower

namespace Membership
abbrev arena : Arena where
  signature := faceSignature.{u}
  Law R := ∀ {V : Type u} [fv : Fintype V] [dv : DecidableEq V] (P : CollapsePair V) (s : Finset V),
    R.readout () V P.retained s ↔ s ∈ P.ambient ∧ s ≠ P.lower ∧ s ≠ P.upper
private theorem bridge : (type_of% (@CollapsePair.mem_retained_iff.{u})) ↔ arena.{u}.Law faceActual := Iff.rfl
private theorem negative : ¬ arena.{u}.Law faceRejected := by
  intro h
  exact (@h sample.V inferInstance inferInstance sample.pair {sample.pair.apex}).mpr
    ((sample.pair.mem_retained_iff _).mp (apex_face sample))
abbrev emptyArena : Arena where
  signature := faceSignature.{u}
  Law R := ∀ {V : Type u} [fv : Fintype V] [dv : DecidableEq V] (P : CollapsePair V),
    ¬ R.readout () V P.retained ∅
private theorem emptyBridge : (type_of% (@CollapsePair.empty_not_mem_retained.{u})) ↔
    emptyArena.{u}.Law faceActual := Iff.rfl
private theorem emptyNegative : ¬ emptyArena.{u}.Law faceAlways := by
  intro h
  exact (@h sample.V inferInstance inferInstance sample.pair) True.intro
end Membership

namespace Inclusion
abbrev signature : Signature where
  Params := Type u
  State V := PreAbstractSimplicialComplex V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ V := PreAbstractSimplicialComplex V → Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} :=
  realize signature (fun _ _ K L => K ≤ L) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [fv : Fintype V] [dv : DecidableEq V] (P : CollapsePair V),
    R.readout () V P.retained P.ambient
private theorem bridge : (type_of% (@CollapsePair.retained_le.{u})) ↔ arena.{u}.Law actual := Iff.rfl
private theorem negative : ¬ arena.{u}.Law rejected := by
  intro h
  exact @h sample.V inferInstance inferInstance sample.pair
private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨sample.V, ⊥, ⊤, ?_⟩
  intro h
  have hh := congrFun h (⊥ : PreAbstractSimplicialComplex sample.V)
  change ((⊥ : PreAbstractSimplicialComplex sample.V) ≤ ⊥) =
    ((⊤ : PreAbstractSimplicialComplex sample.V) ≤ ⊥) at hh
  have bad : (⊤ : PreAbstractSimplicialComplex sample.V) ≤ ⊥ := Eq.mp hh le_rfl
  exact bad (show ({sample.pair.apex} : Finset sample.V) ∈
    (⊤ : PreAbstractSimplicialComplex sample.V) from Finset.singleton_nonempty _)
end Inclusion

namespace Endpoint
abbrev signature : Signature where
  Params := Type u
  State V := Set (V → ℝ)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ V := (V → ℝ) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} :=
  realize signature (fun _ _ K x => x ∈ K) (fun e => nomatch e)
def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [fv : Fintype V] [dv : DecidableEq V] (P : CollapsePair V)
    (x : Space P.ambient), R.readout () V (realization P.retained) (P.endpoint x.val)
private theorem bridge : (type_of% (@CollapsePair.endpoint_mem_retained.{u})) ↔ arena.{u}.Law actual := Iff.rfl
private def samplePoint : Space sample.{u}.pair.ambient := by
  refine ⟨Pi.single sample.pair.apex 1, ?_⟩
  apply (realization_mem_iff _ _).mpr
  refine ⟨{sample.pair.apex}, sample.pair.retained_le (apex_face sample), ?_⟩
  refine ⟨fun v => by
    simp only [Pi.single_apply]
    split_ifs <;> norm_num, ?_, ?_⟩
  · simp
  · intro v hv
    simp only [Finset.mem_singleton] at hv
    simp [hv]
private theorem negative : ¬ arena.{u}.Law rejected := by
  intro h
  exact @h sample.V inferInstance inferInstance sample.pair samplePoint
private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} Unit, ∅, Set.univ, ?_⟩
  intro h
  have hh := congrFun h (0 : ULift.{u} Unit → ℝ)
  change False = True at hh
  exact Eq.mpr hh True.intro
end Endpoint

namespace Nonempty
abbrev signature : Signature where
  Params := Type u
  State V := Finset V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature (fun _ _ s => decide s.Nonempty)
  (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature (fun _ _ _ => false) (fun e =>
  nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [fv : Fintype V] [dv : DecidableEq V] (P : CollapsePair V) {s : Finset V},
    s ∈ P.retained → R.readout () V s = true
private theorem bridge : (type_of% (@CollapsePair.retained_nonempty.{u})) ↔ arena.{u}.Law
  actual := by
  constructor <;> intro h V fv dv P s hs <;> simpa only [actual, realize, decide_eq_true_eq]
    using @h V fv dv P s hs
private theorem negative : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := @h sample.V inferInstance inferInstance sample.pair {sample.pair.apex} (apex_face
    sample)
  change false = true at hh
  cases hh
private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨ULift.{u} Unit, ∅, {⟨()⟩}, ?_⟩
  simp [actual, realize]
def family : Registration arena.{u} (type_of% (@CollapsePair.retained_nonempty.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@CollapsePair.retained_nonempty.{u}), rejected, negative⟩
  sensitivity := ⟨fun _i => ⟨rejected, fun _j h => (h (Subsingleton.elim _ _)).elim, rfl,
    negative⟩, fun e => nomatch e⟩
  dependence := dependence
end Nonempty

namespace Lower
def family : Registration arena.{u} (type_of% (@CollapsePair.lower_mem.{u})) where
  actual := faceActual
  bridge := bridge
  variation := ⟨bridge.mp (@CollapsePair.lower_mem.{u}), faceRejected, negative⟩
  sensitivity := ⟨fun _i => ⟨faceRejected, fun _j h => (h (Subsingleton.elim _ _)).elim, rfl,
    negative⟩, fun e => nomatch e⟩
  dependence := faceDependence
end Lower

namespace Membership
def family : Registration arena.{u} (type_of% (@CollapsePair.mem_retained_iff.{u})) where
  actual := faceActual
  bridge := bridge
  variation := ⟨bridge.mp (@CollapsePair.mem_retained_iff.{u}), faceRejected, negative⟩
  sensitivity := ⟨fun _i => ⟨faceRejected, fun _j h => (h (Subsingleton.elim _ _)).elim, rfl,
    negative⟩, fun e => nomatch e⟩
  dependence := faceDependence
end Membership

namespace Membership
def emptyFamily : Registration emptyArena.{u} (type_of% (@CollapsePair.empty_not_mem_retained.{u})) where
  actual := faceActual
  bridge := emptyBridge
  variation := ⟨emptyBridge.mp (@CollapsePair.empty_not_mem_retained.{u}), faceAlways, emptyNegative⟩
  sensitivity := ⟨fun _i => ⟨faceAlways, fun _j h => (h (Subsingleton.elim _ _)).elim, rfl,
    emptyNegative⟩, fun e => nomatch e⟩
  dependence := faceDependence
end Membership

namespace Inclusion
def family : Registration arena.{u} (type_of% (@CollapsePair.retained_le.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@CollapsePair.retained_le.{u}), rejected, negative⟩
  sensitivity := ⟨fun _i => ⟨rejected, fun _j h => (h (Subsingleton.elim _ _)).elim, rfl,
    negative⟩, fun e => nomatch e⟩
  dependence := dependence
end Inclusion

namespace Endpoint
def family : Registration arena.{u} (type_of% (@CollapsePair.endpoint_mem_retained.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@CollapsePair.endpoint_mem_retained.{u}), rejected, negative⟩
  sensitivity := ⟨fun _i => ⟨rejected, fun _j h => (h (Subsingleton.elim _ _)).elim, rfl,
    negative⟩, fun e => nomatch e⟩
  dependence := dependence
end Endpoint

namespace Lower
def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@CollapsePair.lower_mem.{u}) (Realization faceSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteElementaryCollapse.Lower.registrationUnit
  realizationName := `Reg.D5.S3.Geometry.FiniteElementaryCollapse.Lower.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some faceActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteElementaryCollapse
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Lower

namespace Membership
def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@CollapsePair.mem_retained_iff.{u}) (Realization faceSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteElementaryCollapse.Membership.registrationUnit
  realizationName := `Reg.D5.S3.Geometry.FiniteElementaryCollapse.Membership.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some faceActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteElementaryCollapse
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Membership

namespace Membership
def emptyRegistration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@CollapsePair.empty_not_mem_retained.{u}) (Realization faceSignature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteElementaryCollapse.Membership.emptyRegistrationUnit
  realizationName := `Reg.D5.S3.Geometry.FiniteElementaryCollapse.Membership.emptyFamily
  realizationSource := none
  generated := false
  arena := .source ⟨emptyArena⟩
  objectArena := .source ⟨emptyArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source emptyArena ⟨emptyFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some faceActual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteElementaryCollapse
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Membership

namespace Inclusion
def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@CollapsePair.retained_le.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteElementaryCollapse.Inclusion.registrationUnit
  realizationName := `Reg.D5.S3.Geometry.FiniteElementaryCollapse.Inclusion.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteElementaryCollapse
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Inclusion

namespace Endpoint
def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@CollapsePair.endpoint_mem_retained.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteElementaryCollapse.Endpoint.registrationUnit
  realizationName := `Reg.D5.S3.Geometry.FiniteElementaryCollapse.Endpoint.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteElementaryCollapse
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Endpoint

namespace Nonempty
def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@CollapsePair.retained_nonempty.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteElementaryCollapse.Nonempty.registrationUnit
  realizationName := `Reg.D5.S3.Geometry.FiniteElementaryCollapse.Nonempty.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteElementaryCollapse
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Nonempty

private theorem sample_vertex_face (a : Fin 3) :
    ({ULift.up a} : Finset sample.{u}.V) ∈ sample.pair.retained := by
  refine ⟨Finset.singleton_nonempty _, ?_⟩
  intro h
  have h1 := h (show ULift.up (1 : Fin 3) ∈ sample.pair.lower by simp [sample, samplePair,
    simplexPair])
  have h2 := h (show ULift.up (2 : Fin 3) ∈ sample.pair.lower by simp [sample, samplePair,
    simplexPair])
  have h1' := congrArg ULift.down (Finset.mem_singleton.mp h1)
  have h2' := congrArg ULift.down (Finset.mem_singleton.mp h2)
  have he : (1 : Fin 3) = 2 := h1'.trans h2'.symm
  exact (by decide : (1 : Fin 3) ≠ 2) he

private def sampleVertex (a : Fin 3) : Space sample.{u}.pair.retained := by
  refine ⟨Pi.single (ULift.up a) 1, ?_⟩
  apply (realization_mem_iff _ _).mpr
  refine ⟨{ULift.up a}, sample_vertex_face a, ?_⟩
  refine ⟨fun v => by
    simp only [Pi.single_apply]
    split_ifs <;> norm_num, ?_, ?_⟩
  · simp
  · intro v hv
    simp only [Finset.mem_singleton] at hv
    simp [hv]
private theorem sample_vertices_ne : sampleVertex.{u} 1 ≠ sampleVertex.{u} 2 := by
  intro h
  have hh := congrArg (fun x : Space sample.{u}.pair.retained =>
    x.val (ULift.up.{u, 0} (1 : Fin 3))) h
  change (Pi.single (ULift.up.{u, 0} (1 : Fin 3)) (1 : ℝ) : ULift.{u} (Fin 3) → ℝ)
      (ULift.up.{u, 0} (1 : Fin 3)) =
    (Pi.single (ULift.up.{u, 0} (2 : Fin 3)) (1 : ℝ) : ULift.{u} (Fin 3) → ℝ)
      (ULift.up.{u, 0} (1 : Fin 3)) at hh
  norm_num [Pi.single_apply] at hh

private def apexPoint (p : PairParameters.{u}) : Space p.pair.retained := by
  refine ⟨Pi.single p.pair.apex 1, ?_⟩
  apply (realization_mem_iff _ _).mpr
  refine ⟨{p.pair.apex}, apex_face p, ?_⟩
  refine ⟨fun v => by
    simp only [Pi.single_apply]
    split_ifs <;> norm_num, ?_, ?_⟩
  · simp
  · intro v hv
    simp only [Finset.mem_singleton] at hv
    simp [hv]

namespace Retraction
abbrev signature : Signature where
  Params := PairParameters.{u}
  State p := Space p.pair.retained
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Space p.pair.retained
  Anchor := Empty
  finiteAnchor := inferInstance
def actual : Realization signature.{u} := realize signature
  (fun _ p y => p.pair.retraction (p.pair.inclusion y)) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature (fun _ p _ => apexPoint p) (fun e
  => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [fv : Fintype V] [dv : DecidableEq V] (P : CollapsePair V) (y : Space
    P.retained),
    R.readout () ⟨⟨V, fv, dv⟩, P⟩ y = y
private theorem bridge : (type_of% (@CollapsePair.retraction_inclusion.{u})) ↔ arena.{u}.Law
  actual := Iff.rfl
private theorem negative : ¬ arena.{u}.Law rejected := by
  intro h
  have h1 := @h sample.V inferInstance inferInstance sample.pair (sampleVertex 1)
  have h2 := @h sample.V inferInstance inferInstance sample.pair (sampleVertex 2)
  exact sample_vertices_ne (h1.symm.trans h2)
private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  refine ⟨sample, sampleVertex 1, sampleVertex 2, ?_⟩
  change sample.pair.retraction (sample.pair.inclusion (sampleVertex 1)) ≠
    sample.pair.retraction (sample.pair.inclusion (sampleVertex 2))
  simpa only [CollapsePair.retraction_inclusion] using sample_vertices_ne

def family : Registration arena.{u} (type_of% (@CollapsePair.retraction_inclusion.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (@CollapsePair.retraction_inclusion.{u}), rejected, negative⟩
  sensitivity := ⟨fun _i => ⟨rejected, fun _j h => (h (Subsingleton.elim _ _)).elim, rfl,
    negative⟩, fun e => nomatch e⟩
  dependence := dependence
end Retraction
namespace Retraction
def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@CollapsePair.retraction_inclusion.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteElementaryCollapse.Retraction.unit
  realizationName := `Reg.D5.S3.Geometry.FiniteElementaryCollapse.Retraction.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p y => p.pair.retraction (p.pair.inclusion y)) (fun
    e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Geometry.FiniteElementaryCollapse
    definition := none
    coordinates := #[0, 1, 2, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]
end Retraction
end Reg.D5.S3.Geometry.FiniteElementaryCollapse
