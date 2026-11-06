import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Geometry.FiniteCyclicNoncoverNativeEndpoints

/- UNCOMPILED SOURCE-SHAPED ATTEMPTS. The readouts below are actual source
operands, and the laws retain the source quantifiers and endpoint clauses.
No CompiledSourceScope/Operands/Contract or Scribe validator has run. Actual
correspondence is OPEN; sourceSelection is none. Packed Parameters are a
mathematical family presentation, not an asserted source binder/selector. -/
noncomputable section
open Set Finset
open scoped unitInterval
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Geometry
open _root_.D5.S3.Geometry.FiniteCoordinateGreedyMatching
open _root_.D5.S3.Geometry.FiniteGreedyFamilyTransport
open _root_.D5.S3.Geometry.FiniteIndependentPathGreedy
open _root_.D5.S3.Geometry.FiniteCyclicNoncoverCollapse
open _root_.D5.S3.Geometry.FiniteCyclicNoncoverIntervalPaths
open _root_.D5.S3.Geometry.FiniteCyclicNoncoverUniversalSurvivors
open _root_.D5.S3.Geometry.FiniteCyclicNoncoverNative
open _root_.D5.S3.Geometry.FiniteRelativeSimplicialCollapse
open _root_.D5.S3.Geometry.FiniteElementaryCollapse
open _root_.D5.S3.Geometry.FiniteComponentClosure
open _root_.D5.S3.Geometry.FiniteSimplicialJoin
open _root_.D5.S3.Geometry.FiniteConeCollapse
open _root_.D5.S3.Geometry.FiniteCoordinateTruncation
open _root_.D5.S3.Geometry.FiniteVertexDominationCollapse (faceSet mem_faceSet)
namespace Reg.D5.S3.Geometry.FiniteCyclicNoncoverNativeEndpoints

universe u
open _root_.D5.S3.Geometry.FiniteCyclicNoncoverNativeEndpoints

namespace native_zero
structure Parameters where
  V : Type u
  fv : Fintype V
  dv : DecidableEq V
  q : Nat
  hq : 0 < q
  s : Fin (3*q) ↪ V
attribute [instance] Parameters.fv Parameters.dv

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Finset p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature (fun _ p a => a ∈ X_zero p.q p.hq p.s) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [fv : Fintype V] [dv : DecidableEq V]
    (q : Nat) (hq : 0 < q) (s : Fin (3*q) ↪ V),
    let A := criticalData_zero q hq s
    let K := noncover (show 0 < 3*q by omega) s
    let X := X_zero q hq s
    let C := C_zero q hq s
    let S := main_zero q hq s
    let T := core_zero q hq s
    let PS := mainPairs_zero q hq s
    let PT := corePairs_zero q hq s
    let H := mainSDR_zero q hq s
    let G := coreSDR_zero q hq s
    (∀ a : Finset V, R.readout () ⟨V, fv, dv, q, hq, s⟩ a ↔ a ∈ C ∨ (a.Nonempty ∧ ∃ b ∈ A.critical, a ⊆ b)) ∧
    (∀ a : Finset V, a ∈ C ↔ a ∈ X ∧ a ∉ A.critical) ∧
    (∀ a ∈ A.critical, ∀ b : Finset V, b ⊆ a → (AugmentedFace C b ↔ b ≠ a)) ∧
    (∀ a ∈ X, a.card ≤ 2*q-1) ∧
    (A.critical.card = 2) ∧
    (S.pairs.map CollapsePair.lower).Nodup ∧
    (T.pairs.map CollapsePair.lower).Nodup ∧
    (∀ P ∈ S.pairs, (P.lower, P.apex) ∈ (matching (by omega) s).pairs ∧
      (P.lower, P.upper) ∈ PS) ∧
    (∀ P ∈ T.pairs, (P.lower, P.apex) ∈ (matching (by omega) s).pairs ∧
      (P.lower, P.upper) ∈ PT) ∧
    (∀ e ∈ (matching (by omega) s).pairs,
      ((∃ P ∈ S.pairs, (P.lower, P.apex) = e) ↔ e.1 ∉ X) ∧
      (e.1 ∈ C → ((∃ P ∈ T.pairs, (P.lower, P.apex) = e) ↔ e.1 ∉ vertexComplex A.p))) ∧
    (∀ i, i ≤ S.pairs.length → ∀ a : Finset V,
      a ∈ S.frames.getD i X ↔ a ∈ K ∧
        ∀ P ∈ S.pairs.take i, a ≠ P.lower ∧ a ≠ P.upper) ∧
    (∀ i, i ≤ T.pairs.length → ∀ a : Finset V,
      a ∈ T.frames.getD i (vertexComplex A.p) ↔ a ∈ C ∧
        ∀ P ∈ T.pairs.take i, a ≠ P.lower ∧ a ≠ P.upper) ∧
    (S.frames.getD 0 X = K ∧ T.frames.getD 0 (vertexComplex A.p) = C) ∧
    (S.frames.getD PS.length X = X ∧
      T.frames.getD PT.length (vertexComplex A.p) = vertexComplex (point (by omega) s)) ∧
    (S.frames.length = PS.length+1 ∧ T.frames.length = PT.length+1) ∧
    ((faceSet K).card = (faceSet X).card + 2*PS.length ∧
      (faceSet C).card = 1 + 2*PT.length) ∧
    ((faceSet X).card = (faceSet C).card + 2 ∧
      (faceSet K).card = 1 + 2 + 2*(PS.length+PT.length)) ∧
    (∀ t : I, ∀ x : Space K, x.val ∈ realization X → ∀ v : V,
      (H.homotopy (t, x)).val v = x.val v) ∧
    (∀ t : I, ∀ x : Space C, x.val ∈ realization (vertexComplex A.p) → ∀ v : V,
      (G.homotopy (t, x)).val v = x.val v) ∧
    (∀ x : Space K, ∀ v : V, (H.homotopy (0, x)).val v = x.val v ∧
      (H.homotopy (1, x)).val v = (H.retraction x).val v) ∧
    (∀ x : Space C, ∀ v : V, (G.homotopy (0, x)).val v = x.val v ∧
      (G.homotopy (1, x)).val v = (G.retraction x).val v) ∧
    (∀ y : Space X, ∀ v : V, (H.retraction (realizationInclusion A.X_le y)).val v = y.val v) ∧
    (∀ y : Space (vertexComplex A.p), ∀ v : V,
      (G.retraction (realizationInclusion A.vertex_le_C y)).val v = y.val v) ∧
    (∀ t : I, ∀ x : Space K, ∀ v : V, v ∉ ground s → (H.homotopy (t, x)).val v = 0) ∧
    (∀ t : I, ∀ x : Space C, ∀ v : V, v ∉ ground s → (G.homotopy (t, x)).val v = 0)
private theorem bridge : (type_of% (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverNativeEndpoints.native_zero.{u})) ↔ arena.{u}.Law actual := Iff.rfl
private def testEmbedding : Fin 3 ↪ ULift.{u} (Fin 3) :=
  ⟨ULift.up, fun _ _ he => congrArg ULift.down he⟩
private def testParameters : Parameters.{u} :=
  ⟨ULift.{u} (Fin 3), inferInstance, inferInstance, 1, by omega, testEmbedding⟩
private def presentState : signature.State testParameters := {point (by omega) testEmbedding}
private def absentState : signature.State testParameters := ∅
private theorem present : actual.{u}.readout () testParameters presentState :=
  (criticalData_zero 1 (by omega) testEmbedding).point_in_X
private theorem absent : ¬ actual.{u}.readout () testParameters absentState := by
  intro h
  exact Finset.not_nonempty_empty
    (((X_zero 1 (by omega) testEmbedding).isRelLowerSet_faces h).1)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h (V := ULift.{u} (Fin 3)) 1 (by omega) testEmbedding
  exact (hh.1 {point (by omega) testEmbedding}).mpr
    (Or.inl (criticalData_zero 1 (by omega) testEmbedding).point_in_C)

private theorem source_law : arena.{u}.Law actual := bridge.mp (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverNativeEndpoints.native_zero.{u})

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverNativeEndpoints.native_zero.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨source_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    cases i
    refine ⟨testParameters, presentState, absentState, ?_⟩
    intro he
    exact absent (he ▸ present)

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverNativeEndpoints.native_zero.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverNativeEndpoints.native_zero.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverNativeEndpoints.native_zero.family
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
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end native_zero

namespace native_one
structure Parameters where
  V : Type u
  fv : Fintype V
  dv : DecidableEq V
  q : Nat
  hq : 0 < q
  s : Fin (3*q+1) ↪ V
attribute [instance] Parameters.fv Parameters.dv

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Finset p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature (fun _ p a => a ∈ X_one p.q p.hq p.s) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [fv : Fintype V] [dv : DecidableEq V]
    (q : Nat) (hq : 0 < q) (s : Fin (3*q+1) ↪ V),
    let A := criticalData_one q hq s
    let K := noncover (show 0 < 3*q+1 by omega) s
    let X := X_one q hq s
    let C := C_one q hq s
    let S := main_one q hq s
    let T := core_one q hq s
    let PS := mainPairs_one q hq s
    let PT := corePairs_one q hq s
    let H := mainSDR_one q hq s
    let G := coreSDR_one q hq s
    (∀ a : Finset V, R.readout () ⟨V, fv, dv, q, hq, s⟩ a ↔ a ∈ C ∨ (a.Nonempty ∧ ∃ b ∈ A.critical, a ⊆ b)) ∧
    (∀ a : Finset V, a ∈ C ↔ a ∈ X ∧ a ∉ A.critical) ∧
    (∀ a ∈ A.critical, ∀ b : Finset V, b ⊆ a → (AugmentedFace C b ↔ b ≠ a)) ∧
    (∀ a ∈ X, a.card ≤ 2*q) ∧
    (A.critical.card = 1) ∧
    (S.pairs.map CollapsePair.lower).Nodup ∧
    (T.pairs.map CollapsePair.lower).Nodup ∧
    (∀ P ∈ S.pairs, (P.lower, P.apex) ∈ (matching (by omega) s).pairs ∧
      (P.lower, P.upper) ∈ PS) ∧
    (∀ P ∈ T.pairs, (P.lower, P.apex) ∈ (matching (by omega) s).pairs ∧
      (P.lower, P.upper) ∈ PT) ∧
    (∀ e ∈ (matching (by omega) s).pairs,
      ((∃ P ∈ S.pairs, (P.lower, P.apex) = e) ↔ e.1 ∉ X) ∧
      (e.1 ∈ C → ((∃ P ∈ T.pairs, (P.lower, P.apex) = e) ↔ e.1 ∉ vertexComplex A.p))) ∧
    (∀ i, i ≤ S.pairs.length → ∀ a : Finset V,
      a ∈ S.frames.getD i X ↔ a ∈ K ∧
        ∀ P ∈ S.pairs.take i, a ≠ P.lower ∧ a ≠ P.upper) ∧
    (∀ i, i ≤ T.pairs.length → ∀ a : Finset V,
      a ∈ T.frames.getD i (vertexComplex A.p) ↔ a ∈ C ∧
        ∀ P ∈ T.pairs.take i, a ≠ P.lower ∧ a ≠ P.upper) ∧
    (S.frames.getD 0 X = K ∧ T.frames.getD 0 (vertexComplex A.p) = C) ∧
    (S.frames.getD PS.length X = X ∧
      T.frames.getD PT.length (vertexComplex A.p) = vertexComplex (point (by omega) s)) ∧
    (S.frames.length = PS.length+1 ∧ T.frames.length = PT.length+1) ∧
    ((faceSet K).card = (faceSet X).card + 2*PS.length ∧
      (faceSet C).card = 1 + 2*PT.length) ∧
    ((faceSet X).card = (faceSet C).card + 1 ∧
      (faceSet K).card = 1 + 1 + 2*(PS.length+PT.length)) ∧
    (∀ t : I, ∀ x : Space K, x.val ∈ realization X → ∀ v : V,
      (H.homotopy (t, x)).val v = x.val v) ∧
    (∀ t : I, ∀ x : Space C, x.val ∈ realization (vertexComplex A.p) → ∀ v : V,
      (G.homotopy (t, x)).val v = x.val v) ∧
    (∀ x : Space K, ∀ v : V, (H.homotopy (0, x)).val v = x.val v ∧
      (H.homotopy (1, x)).val v = (H.retraction x).val v) ∧
    (∀ x : Space C, ∀ v : V, (G.homotopy (0, x)).val v = x.val v ∧
      (G.homotopy (1, x)).val v = (G.retraction x).val v) ∧
    (∀ y : Space X, ∀ v : V, (H.retraction (realizationInclusion A.X_le y)).val v = y.val v) ∧
    (∀ y : Space (vertexComplex A.p), ∀ v : V,
      (G.retraction (realizationInclusion A.vertex_le_C y)).val v = y.val v) ∧
    (∀ t : I, ∀ x : Space K, ∀ v : V, v ∉ ground s → (H.homotopy (t, x)).val v = 0) ∧
    (∀ t : I, ∀ x : Space C, ∀ v : V, v ∉ ground s → (G.homotopy (t, x)).val v = 0)
private theorem bridge : (type_of% (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverNativeEndpoints.native_one.{u})) ↔ arena.{u}.Law actual := Iff.rfl
private def testEmbedding : Fin 4 ↪ ULift.{u} (Fin 4) :=
  ⟨ULift.up, fun _ _ he => congrArg ULift.down he⟩
private def testParameters : Parameters.{u} :=
  ⟨ULift.{u} (Fin 4), inferInstance, inferInstance, 1, by omega, testEmbedding⟩
private def presentState : signature.State testParameters := {point (by omega) testEmbedding}
private def absentState : signature.State testParameters := ∅
private theorem present : actual.{u}.readout () testParameters presentState :=
  (criticalData_one 1 (by omega) testEmbedding).point_in_X
private theorem absent : ¬ actual.{u}.readout () testParameters absentState := by
  intro h
  exact Finset.not_nonempty_empty
    (((X_one 1 (by omega) testEmbedding).isRelLowerSet_faces h).1)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h (V := ULift.{u} (Fin 4)) 1 (by omega) testEmbedding
  exact (hh.1 {point (by omega) testEmbedding}).mpr
    (Or.inl (criticalData_one 1 (by omega) testEmbedding).point_in_C)

private theorem source_law : arena.{u}.Law actual := bridge.mp (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverNativeEndpoints.native_one.{u})

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverNativeEndpoints.native_one.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨source_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    cases i
    refine ⟨testParameters, presentState, absentState, ?_⟩
    intro he
    exact absent (he ▸ present)

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverNativeEndpoints.native_one.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverNativeEndpoints.native_one.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverNativeEndpoints.native_one.family
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
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end native_one

namespace native_two
structure Parameters where
  V : Type u
  fv : Fintype V
  dv : DecidableEq V
  q : Nat
  hq : 0 < q
  s : Fin (3*q+2) ↪ V
attribute [instance] Parameters.fv Parameters.dv

abbrev signature : Signature where
  Params := Parameters.{u}
  State p := Finset p.V
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} := realize signature (fun _ p a => a ∈ X_two p.q p.hq p.s) (fun e => nomatch e)
def rejected : Realization signature.{u} := realize signature (fun _ _ _ => False) (fun e => nomatch e)
abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {V : Type u} [fv : Fintype V] [dv : DecidableEq V]
    (q : Nat) (hq : 0 < q) (s : Fin (3*q+2) ↪ V),
    let A := criticalData_two q hq s
    let K := noncover (show 0 < 3*q+2 by omega) s
    let X := X_two q hq s
    let C := C_two q hq s
    let S := main_two q hq s
    let T := core_two q hq s
    let PS := mainPairs_two q hq s
    let PT := corePairs_two q hq s
    let H := mainSDR_two q hq s
    let G := coreSDR_two q hq s
    (∀ a : Finset V, R.readout () ⟨V, fv, dv, q, hq, s⟩ a ↔ a ∈ C ∨ (a.Nonempty ∧ ∃ b ∈ A.critical, a ⊆ b)) ∧
    (∀ a : Finset V, a ∈ C ↔ a ∈ X ∧ a ∉ A.critical) ∧
    (∀ a ∈ A.critical, ∀ b : Finset V, b ⊆ a → (AugmentedFace C b ↔ b ≠ a)) ∧
    (∀ a ∈ X, a.card ≤ 2*q) ∧
    (A.critical.card = 1) ∧
    (S.pairs.map CollapsePair.lower).Nodup ∧
    (T.pairs.map CollapsePair.lower).Nodup ∧
    (∀ P ∈ S.pairs, (P.lower, P.apex) ∈ (matching (by omega) s).pairs ∧
      (P.lower, P.upper) ∈ PS) ∧
    (∀ P ∈ T.pairs, (P.lower, P.apex) ∈ (matching (by omega) s).pairs ∧
      (P.lower, P.upper) ∈ PT) ∧
    (∀ e ∈ (matching (by omega) s).pairs,
      ((∃ P ∈ S.pairs, (P.lower, P.apex) = e) ↔ e.1 ∉ X) ∧
      (e.1 ∈ C → ((∃ P ∈ T.pairs, (P.lower, P.apex) = e) ↔ e.1 ∉ vertexComplex A.p))) ∧
    (∀ i, i ≤ S.pairs.length → ∀ a : Finset V,
      a ∈ S.frames.getD i X ↔ a ∈ K ∧
        ∀ P ∈ S.pairs.take i, a ≠ P.lower ∧ a ≠ P.upper) ∧
    (∀ i, i ≤ T.pairs.length → ∀ a : Finset V,
      a ∈ T.frames.getD i (vertexComplex A.p) ↔ a ∈ C ∧
        ∀ P ∈ T.pairs.take i, a ≠ P.lower ∧ a ≠ P.upper) ∧
    (S.frames.getD 0 X = K ∧ T.frames.getD 0 (vertexComplex A.p) = C) ∧
    (S.frames.getD PS.length X = X ∧
      T.frames.getD PT.length (vertexComplex A.p) = vertexComplex (point (by omega) s)) ∧
    (S.frames.length = PS.length+1 ∧ T.frames.length = PT.length+1) ∧
    ((faceSet K).card = (faceSet X).card + 2*PS.length ∧
      (faceSet C).card = 1 + 2*PT.length) ∧
    ((faceSet X).card = (faceSet C).card + 1 ∧
      (faceSet K).card = 1 + 1 + 2*(PS.length+PT.length)) ∧
    (∀ t : I, ∀ x : Space K, x.val ∈ realization X → ∀ v : V,
      (H.homotopy (t, x)).val v = x.val v) ∧
    (∀ t : I, ∀ x : Space C, x.val ∈ realization (vertexComplex A.p) → ∀ v : V,
      (G.homotopy (t, x)).val v = x.val v) ∧
    (∀ x : Space K, ∀ v : V, (H.homotopy (0, x)).val v = x.val v ∧
      (H.homotopy (1, x)).val v = (H.retraction x).val v) ∧
    (∀ x : Space C, ∀ v : V, (G.homotopy (0, x)).val v = x.val v ∧
      (G.homotopy (1, x)).val v = (G.retraction x).val v) ∧
    (∀ y : Space X, ∀ v : V, (H.retraction (realizationInclusion A.X_le y)).val v = y.val v) ∧
    (∀ y : Space (vertexComplex A.p), ∀ v : V,
      (G.retraction (realizationInclusion A.vertex_le_C y)).val v = y.val v) ∧
    (∀ t : I, ∀ x : Space K, ∀ v : V, v ∉ ground s → (H.homotopy (t, x)).val v = 0) ∧
    (∀ t : I, ∀ x : Space C, ∀ v : V, v ∉ ground s → (G.homotopy (t, x)).val v = 0)
private theorem bridge : (type_of% (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverNativeEndpoints.native_two.{u})) ↔ arena.{u}.Law actual := Iff.rfl
private def testEmbedding : Fin 5 ↪ ULift.{u} (Fin 5) :=
  ⟨ULift.up, fun _ _ he => congrArg ULift.down he⟩
private def testParameters : Parameters.{u} :=
  ⟨ULift.{u} (Fin 5), inferInstance, inferInstance, 1, by omega, testEmbedding⟩
private def presentState : signature.State testParameters := {point (by omega) testEmbedding}
private def absentState : signature.State testParameters := ∅
private theorem present : actual.{u}.readout () testParameters presentState :=
  (criticalData_two 1 (by omega) testEmbedding).point_in_X
private theorem absent : ¬ actual.{u}.readout () testParameters absentState := by
  intro h
  exact Finset.not_nonempty_empty
    (((X_two 1 (by omega) testEmbedding).isRelLowerSet_faces h).1)
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h (V := ULift.{u} (Fin 5)) 1 (by omega) testEmbedding
  exact (hh.1 {point (by omega) testEmbedding}).mpr
    (Or.inl (criticalData_two 1 (by omega) testEmbedding).point_in_C)

private theorem source_law : arena.{u}.Law actual := bridge.mp (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverNativeEndpoints.native_two.{u})

def family : Registration arena.{u} (type_of% (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverNativeEndpoints.native_two.{u})) where
  actual := actual
  bridge := bridge
  variation := ⟨source_law, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j h => (h (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := by
    intro i
    cases i
    refine ⟨testParameters, presentState, absentState, ?_⟩
    intro he
    exact absent (he ▸ present)

def registration : LeanInformationAudit.Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@_root_.D5.S3.Geometry.FiniteCyclicNoncoverNativeEndpoints.native_two.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverNativeEndpoints.native_two.__information_unit
  realizationName := `Reg.D5.S3.Geometry.FiniteCyclicNoncoverNativeEndpoints.native_two.family
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
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

end native_two

end Reg.D5.S3.Geometry.FiniteCyclicNoncoverNativeEndpoints
