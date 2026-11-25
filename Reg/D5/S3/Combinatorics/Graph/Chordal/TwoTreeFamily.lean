import D5.S3.Combinatorics.Graph.Chordal.TwoTreeFamily
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import Mathlib.Algebra.Module.ULift

/-! Source-bound observations of circulation coordinates and graph triangles. -/

namespace Reg.D5.S3.Combinatorics.Graph.Chordal.TwoTreeFamily

open SimpleGraph

local instance : DecidableRel (twoTree 0).Adj := Top.adjDecidable (Fin 3)
open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

open scoped BigOperators

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v

abbrev coordinateParams := Σ R : Type u, Σ _ : CommRing R, ℕ

abbrev coordinateSignature : Signature where
  Params := coordinateParams.{u}
  State p := TwoTreeTriangles p.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := TwoTreeTriangles p.2.2 → p.1
  Anchor := Empty
  finiteAnchor := inferInstance

def coordinateReader (p : coordinateParams.{u}) (i : TwoTreeTriangles p.2.2) :
    TwoTreeTriangles p.2.2 → p.1 := by
  rcases p with ⟨R, inst, d⟩
  letI : CommRing R := inst
  exact twoTreeCirculationCoordinates R d (twoTreeTriangleChain R d i)

def coordinateActual : Realization coordinateSignature.{u} :=
  realize coordinateSignature (fun _ p i => coordinateReader p i) (fun a => nomatch a)

def coordinateZero : Realization coordinateSignature.{u} :=
  realize coordinateSignature (fun _ p _ _ => by letI := p.2.1; exact 0) (fun a => nomatch a)

abbrev coordinateArena : Arena where
  signature := coordinateSignature.{u}
  Law F := ∀ (R : Type u) [inst : CommRing R] (d : ℕ) (i : TwoTreeTriangles d),
    F.readout () ⟨R, inst, d⟩ i = Pi.single i 1

private theorem coordinate_zero_rejected : ¬ coordinateArena.{u}.Law coordinateZero.{u} := by
  intro h
  have h0 := congrFun (h (ULift.{u} ℤ) 0 ()) ()
  change (0 : ULift.{u} ℤ) = (Pi.single () 1 : Unit → ULift.{u} ℤ) () at h0
  rw [Pi.single_eq_same] at h0
  exact zero_ne_one h0

def coordinateEvidence : Registration coordinateArena.{u}
    (type_of% twoTree_triangle_chain_coordinate.{u}) where
  actual := coordinateActual
  bridge := Iff.rfl
  variation := ⟨twoTree_triangle_chain_coordinate.{u}, coordinateZero, coordinate_zero_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨coordinateZero, ?_, rfl, coordinate_zero_rejected⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · exact fun a => nomatch a
  dependence := by
    intro i
    let R := ULift.{u} ℤ
    let a : TwoTreeTriangles 1 := .inl ()
    let b : TwoTreeTriangles 1 := .inr (0 : Fin 3)
    refine ⟨⟨R, inferInstance, 1⟩, a, b, ?_⟩
    change twoTreeCirculationCoordinates R 1 (twoTreeTriangleChain R 1 a) ≠
      twoTreeCirculationCoordinates R 1 (twoTreeTriangleChain R 1 b)
    rw [twoTree_triangle_chain_coordinate, twoTree_triangle_chain_coordinate]
    intro eq
    have h := congrFun eq a
    simp [a, b] at h

abbrev fillingSignature : Signature where
  Params := ℕ
  State d := TwoTreeCirculation ℝ d
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def fillingActual : Realization fillingSignature :=
  realize fillingSignature (fun _ d z => twoTreeFillingNorm d z) (fun a => nomatch a)

def fillingZero : Realization fillingSignature :=
  realize fillingSignature (fun _ _ _ => 0) (fun a => nomatch a)

abbrev fillingArena : Arena where
  signature := fillingSignature
  Law F := ∀ (d : ℕ) (z : TwoTreeCirculation ℝ d),
    F.readout () d z = ‖WithLp.toLp 1 (twoTreeCirculationCoordinates ℝ d z)‖

private theorem unit_core_norm :
    ‖WithLp.toLp 1 (twoTreeCirculationCoordinates ℝ 0 (twoTreeTriangleChain ℝ 0 ()))‖ = 1 := by
  rw [twoTree_triangle_chain_coordinate]
  change ‖(PiLp.single 1 () (1 : ℝ) : PiLp 1 (fun _ : Unit => ℝ))‖ = 1
  simp

private theorem filling_zero_rejected : ¬ fillingArena.Law fillingZero := by
  intro h
  have h0 := h 0 (twoTreeTriangleChain ℝ 0 ())
  change (0 : ℝ) = _ at h0
  rw [unit_core_norm] at h0
  exact zero_ne_one h0

def fillingEvidence : Registration fillingArena (type_of% twoTree_filling_norm_eq) where
  actual := fillingActual
  bridge := Iff.rfl
  variation := ⟨twoTree_filling_norm_eq, fillingZero, filling_zero_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨fillingZero, ?_, rfl, filling_zero_rejected⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · exact fun a => nomatch a
  dependence := by
    intro i
    refine ⟨0, 0, twoTreeTriangleChain ℝ 0 (), ?_⟩
    change twoTreeFillingNorm 0 0 ≠ twoTreeFillingNorm 0 (twoTreeTriangleChain ℝ 0 ())
    rw [twoTree_filling_norm_eq, twoTree_filling_norm_eq, unit_core_norm, map_zero, WithLp.toLp_zero,
      norm_zero]
    exact zero_ne_one

abbrev triangleSignature : Signature where
  Params := ℕ
  State d := TwoTreeTriangles d
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ d := Set (TwoTreeV d)
  Anchor := Empty
  finiteAnchor := inferInstance

def triangleActual : Realization triangleSignature :=
  realize triangleSignature (fun _ d i => twoTreeTriangleVertices d i) (fun a => nomatch a)

def triangleEmpty : Realization triangleSignature :=
  realize triangleSignature (fun _ _ _ => ∅) (fun a => nomatch a)

abbrev triangleArena : Arena where
  signature := triangleSignature
  Law F := ∀ d : ℕ,
    (∀ a b c, (twoTree d).Adj a b → (twoTree d).Adj b c → (twoTree d).Adj a c →
      ∃ i : TwoTreeTriangles d, F.readout () d i = {a, b, c}) ∧
    (∀ i : TwoTreeTriangles d, let (a, b, c) := twoTreeOrientedTriangle d i
      (twoTree d).Adj a b ∧ (twoTree d).Adj b c ∧ (twoTree d).Adj c a)

private theorem triangle_empty_rejected : ¬ triangleArena.Law triangleEmpty := by
  intro h
  obtain ⟨i, he⟩ := (h 0).1 0 1 2 (by decide) (by decide) (by decide)
  change (∅ : Set (Fin 3)) = {0, 1, 2} at he
  have hmem : (0 : Fin 3) ∈ ({0, 1, 2} : Set (Fin 3)) := by simp
  rw [← he] at hmem
  exact hmem

def triangleEvidence : Registration triangleArena (type_of% twoTree_triangles_classify) where
  actual := triangleActual
  bridge := Iff.rfl
  variation := ⟨twoTree_triangles_classify, triangleEmpty, triangle_empty_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨triangleEmpty, ?_, rfl, triangle_empty_rejected⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · exact fun a => nomatch a
  dependence := by
    intro i
    let a : TwoTreeTriangles 1 := .inr (0 : Fin 3)
    let b : TwoTreeTriangles 1 := .inr (1 : Fin 3)
    let w : TwoTreeV 1 := .inr (0 : Fin 3)
    refine ⟨1, a, b, ?_⟩
    change twoTreeTriangleVertices 1 a ≠ twoTreeTriangleVertices 1 b
    intro h
    have hw : w ∈ twoTreeTriangleVertices 1 a := by
      simp [w, a, twoTreeTriangleVertices, twoTreeOrientedTriangle]
    rw [h] at hw
    simpa [w, b, twoTreeTriangleVertices, twoTreeOrientedTriangle] using hw

abbrev pairingParams :=
  Σ R : Type u, Σ E : Type v, Σ r : CommRing R, Σ e : AddCommGroup E,
    Σ _ : @Module R E r.toSemiring e.toAddCommMonoid, Σ d : ℕ, TwoTreeTriangles d → E

abbrev pairingSignature : Signature where
  Params := pairingParams.{u, v}
  State p := by
    rcases p with ⟨R, E, ring, addGroup, inst, d, τ⟩
    letI : CommRing R := ring
    exact ↥(TwoTreeCirculation R d)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.2.1
  Anchor := Empty
  finiteAnchor := inferInstance

def pairingReader (p : pairingParams.{u, v}) (z : pairingSignature.State p) : p.2.1 := by
  rcases p with ⟨R, E, ring, addGroup, inst, d, τ⟩
  letI : CommRing R := ring
  letI : AddCommGroup E := addGroup
  letI : Module R E := inst
  exact ∑ i : TwoTreeTriangles d, twoTreeCirculationCoordinates R d z i • τ i

def pairingActual : Realization pairingSignature.{u, v} :=
  realize pairingSignature (fun _ p z => pairingReader p z) (fun a => nomatch a)

def pairingZero : Realization pairingSignature.{u, v} :=
  realize pairingSignature (fun _ p _ => by letI := p.2.2.2.1; exact 0) (fun a => nomatch a)

abbrev pairingArena : Arena where
  signature := pairingSignature.{u,v}
  Law F := ∀ {R : Type u} {E : Type v} [r : CommRing R] [a : AddCommGroup E] [m : Module R E]
    (d : ℕ) (τ : TwoTreeTriangles d → E) (z : TwoTreeCirculation R d),
    (∑ e : TwoTreeEdges d, z.val e •
      twoTreeTriangleGain d τ (twoTreeEdgeSource d e) (twoTreeEdgeTarget d e)) =
        F.readout () ⟨R, E, r, a, m, d, τ⟩ z

private theorem unit_pairing :
    pairingReader ⟨ULift.{u} ℤ, ULift.{v} ℤ, inferInstance, inferInstance, inferInstance, 0,
      fun _ => 1⟩ (twoTreeTriangleChain (ULift.{u} ℤ) 0 ()) = 1 := by
  change (∑ i : Unit,
    twoTreeCirculationCoordinates (ULift.{u} ℤ) 0 (twoTreeTriangleChain (ULift.{u} ℤ) 0 ()) i •
      (1 : ULift.{v} ℤ)) = 1
  rw [twoTree_triangle_chain_coordinate]
  simp

private theorem pairing_zero_rejected : ¬ pairingArena.{u, v}.Law pairingZero.{u, v} := by
  intro h
  have h0 := @h (ULift.{u} ℤ) (ULift.{v} ℤ) _ _ _ 0 (fun _ => 1)
    (twoTreeTriangleChain (ULift.{u} ℤ) 0 ())
  rw [twoTree_triangle_gain_pairing] at h0
  change pairingReader ⟨ULift.{u} ℤ, ULift.{v} ℤ, inferInstance, inferInstance, inferInstance,
    0, fun _ => 1⟩ (twoTreeTriangleChain (ULift.{u} ℤ) 0 ()) = 0 at h0
  exact one_ne_zero (unit_pairing.{u,v}.symm.trans h0)

def pairingEvidence : Registration pairingArena.{u,v} (type_of% (@twoTree_triangle_gain_pairing.{u,v})) where
  actual := pairingActual
  bridge := Iff.rfl
  variation := ⟨twoTree_triangle_gain_pairing.{u,v}, pairingZero, pairing_zero_rejected⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨pairingZero, ?_, rfl, pairing_zero_rejected⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · exact fun a => nomatch a
  dependence := by
    intro i
    let p : pairingParams.{u,v} :=
      ⟨ULift.{u} ℤ, ULift.{v} ℤ, inferInstance, inferInstance, inferInstance, 0, fun _ => 1⟩
    refine ⟨p, twoTreeTriangleChain (ULift.{u} ℤ) 0 (), 0, ?_⟩
    change pairingReader p (twoTreeTriangleChain (ULift.{u} ℤ) 0 ()) ≠ pairingReader p 0
    rw [show pairingReader p (twoTreeTriangleChain (ULift.{u} ℤ) 0 ()) = 1 from unit_pairing]
    change (1 : ULift.{v} ℤ) ≠ ∑ i : Unit,
      twoTreeCirculationCoordinates (ULift.{u} ℤ) 0 0 i • (1 : ULift.{v} ℤ)
    simp


def coordinateRegistration : Contract.Registration.{_,_,_,0,0,0,u+1,0,0,u,0,0}
    (@SimpleGraph.twoTree_triangle_chain_coordinate.{u}) (Realization coordinateSignature.{u}) Unit Unit where
  unitName := `SimpleGraph.twoTree_triangle_chain_coordinate.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.TwoTreeFamily.coordinateEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨coordinateArena.{u}⟩
  objectArena := .source ⟨coordinateArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source coordinateArena.{u} ⟨coordinateEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize coordinateSignature.{u} (fun _ p i => coordinateReader p i) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.TwoTreeFamily
    definition := none
    coordinates := #[0, 2]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def fillingRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,0,0,0}
    (@SimpleGraph.twoTree_filling_norm_eq) (Realization fillingSignature) Unit Unit where
  unitName := `SimpleGraph.twoTree_filling_norm_eq.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.TwoTreeFamily.fillingEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨fillingArena⟩
  objectArena := .source ⟨fillingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source fillingArena ⟨fillingEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize fillingSignature (fun _ d z => twoTreeFillingNorm d z) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.TwoTreeFamily
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def triangleRegistration : Contract.Registration.{_,_,_,0,0,0,_,_,_,0,0,0}
    (@SimpleGraph.twoTree_triangles_classify) (Realization triangleSignature) Unit Unit where
  unitName := `SimpleGraph.twoTree_triangles_classify.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.TwoTreeFamily.triangleEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨triangleArena⟩
  objectArena := .source ⟨triangleArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source triangleArena ⟨triangleEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize triangleSignature (fun _ d i => twoTreeTriangleVertices d i) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.TwoTreeFamily
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "fn", "arg", "body", "body", "body", "body", "body", "body", "arg", "body", "fn", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def pairingRegistration : Contract.Registration.{_,_,_,0,0,0,_,u,0,v,0,0}
    (@SimpleGraph.twoTree_triangle_gain_pairing.{u, v}) (Realization pairingSignature.{u, v}) Unit Unit where
  unitName := `SimpleGraph.twoTree_triangle_gain_pairing.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.Chordal.TwoTreeFamily.pairingEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨pairingArena.{u, v}⟩
  objectArena := .source ⟨pairingArena.{u, v}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source pairingArena.{u, v} ⟨pairingEvidence.{u, v}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize pairingSignature.{u, v} (fun _ p z => pairingReader p z) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.Chordal.TwoTreeFamily
    definition := none
    coordinates := #[0, 1, 5, 6]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 7
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Combinatorics.Graph.Chordal.TwoTreeFamily
