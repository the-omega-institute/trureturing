import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily
import D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSwitchingFiber

/-! The integer negative-degree vector used in testing the joint fiber. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.checkUnivs false

open scoped Matrix
open LinearMap LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedCycleRank
open _root_.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSwitchingFiber

namespace Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSwitchingFiber

private abbrev rowSignature.{u} : Signature.{u + 1, u, 0, u, 0} where
  Params := Σ V : Type u, Σ _ : Fintype V, Σ _ : DecidableEq V,
    Σ G : SimpleGraph V, DecidableRel G.Adj
  State p := p.2.2.2.1.edgeSet → ZMod 2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := p.1 → ℤ
  Anchor := Empty
  finiteAnchor := inferInstance

private def rowActual.{u} : Realization rowSignature.{u} :=
  realize rowSignature
    (fun _ p w => @negativeDegree _ p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 w) Empty.elim

private def rowRejected.{u} : Realization rowSignature.{u} :=
  realize rowSignature (fun _ _ _ => 0) Empty.elim

private abbrev rowArena.{u} : Arena where
  signature := rowSignature.{u}
  Law readout := ∀ {V : Type u} [vType : Fintype V] [vEq : DecidableEq V] (G : SimpleGraph V)
    [adj : DecidableRel G.Adj] (F : Set G.edgeSet)
    (s : G.edgeSet → ZMod 2) (q : V → ℤ) (f : F → ZMod 2),
    let B := incidence G
    let T := Bᵀ.mulVecLin
    let J := jointMap B F
    let b := ((fun v => (q v : ZMod 2)), f)
    let S := ker J
    let D := S ⊓ range T
    let R := (bicycles B).mkQ.domRestrict (S.comap (Cycles B).subtype)
    let W : Set (G.edgeSet → ZMod 2) := {w | (∃ z, w = s + T z) ∧ J w = b}
    (W.Nonempty ↔ b - J s ∈ range (J.comp T)) ∧
    (∀ w₀ ∈ W, ∀ w, w ∈ W ↔ ∃ d : D, w = w₀ + d.val) ∧
    (Module.finrank (ZMod 2) D + Module.finrank (ZMod 2) (range (J.comp T)) = B.rank) ∧
    (Module.finrank (ZMod 2) D + Module.finrank (ZMod 2) (range R) =
      Module.finrank (ZMod 2) S) ∧
    ((∀ w, negativeDegree G w = q → (fun e : F => w e.val) = f) →
      ((∃ z, signedRow G (s + T z) = fun v => (G.degree v : ℤ) - 2 * q v) ↔
        ∃ w ∈ W, readout.readout () ⟨V, vType, vEq, G, adj⟩ w = q))

private abbrev oneEdge.{u} : SimpleGraph (ULift.{u} Bool) := ⊤

private theorem rowRejected_law.{u} : ¬ rowArena.{u}.Law rowRejected.{u} := by
  intro h
  have hFreeze : ∀ w, negativeDegree oneEdge.{u} w = (fun _ => 1) →
      (fun e : (∅ : Set oneEdge.{u}.edgeSet) => w e.val) = fun _ => 0 := by
    intro w _
    funext e
    exact e.property.elim
  have hLaw := (h oneEdge.{u} ∅ (fun _ => 1) (fun _ => 1) (fun _ => 0)).2.2.2.2 hFreeze
  have hRows :
      signedRow oneEdge.{u}
        ((fun _ => 1) + (incidence oneEdge.{u})ᵀ.mulVecLin 0) =
        fun v => (oneEdge.{u}.degree v : ℤ) - 2 * 1 := by
    funext v
    cases v with
    | up v => cases v <;> decide
  obtain ⟨_, _, hq⟩ := hLaw.mp ⟨0, hRows⟩
  exact (by decide : (0 : ℤ) ≠ 1) (congrFun hq ⟨false⟩)

def rowEvidence.{u} : Registration rowArena.{u} (type_of% (@joint_switching_fiber.{u})) where
  actual := rowActual
  bridge := Iff.rfl
  variation := ⟨joint_switching_fiber, rowRejected, rowRejected_law⟩
  sensitivity := by
    constructor
    · intro role
      exact ⟨rowRejected, fun other h => (h (Subsingleton.elim other role)).elim,
        rfl, rowRejected_law⟩
    · intro anchor
      exact nomatch anchor
  dependence := by
    rintro ⟨⟩
    refine ⟨⟨ULift.{u} Bool, inferInstance, inferInstance, oneEdge.{u}, inferInstance⟩,
      (fun _ => 0), (fun _ => 1), ?_⟩
    intro eqRows
    exact (by decide :
      negativeDegree oneEdge.{u} (fun _ => 0) ⟨false⟩ ≠
        negativeDegree oneEdge.{u} (fun _ => 1) ⟨false⟩) (congrFun eqRows ⟨false⟩)

def rowRegistration.{u} : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@joint_switching_fiber.{u}) (Realization rowSignature.{u}) Unit Unit where
  unitName := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSwitchingFiber.joint_switching_fiber.__information_unit
  realizationName := `Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSwitchingFiber.rowEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨rowArena.{u}⟩
  objectArena := .source ⟨rowArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source rowArena.{u} ⟨rowEvidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize rowSignature.{u}
    (fun _ p w => @negativeDegree _ p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2 w) Empty.elim)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSwitchingFiber
    definition := none
    coordinates := #[0, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg", "arg", "body", "arg", "arg", "body", "arg", "fn", "arg"]
      stateBinder := 18
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Combinatorics.Graph.HypercubeCritical.ComponentBoundary.Q9FoldedSwitchingFiber
