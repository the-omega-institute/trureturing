import D5.S3.ConceptDynamics.Coding.ResetTwoStepArithmetic
import Reg.D5.S3.ConceptDynamics.Coding.ResetTwoStepCarrier
import Reg.Support.DependentFamily
import D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect
import LeanInformationAuditInterface.Contract.Registration

open _root_.D5.S3.ConceptDynamics.Coding.ResetNumberedHistories
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.ConceptDynamics.Coding.ResetTwoStepArithmetic
noncomputable section

open _root_.D5.S3.ConceptDynamics.Coding.ResetNumberedHistories.TwoStep

abbrev exchangeSignature : Signature where
  Params := {q : ℕ // 4 ∣ q}
  State q := Word q.val
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ q := Word q.val
  Anchor := Empty
  finiteAnchor := inferInstance

def exchangeActual : Realization exchangeSignature :=
  realize exchangeSignature (fun _ q w => exchange q.property (exchange q.property w))
    (fun e => nomatch e)
def exchangeRejected : Realization exchangeSignature :=
  realize exchangeSignature (fun _ q w => exchange q.property w) (fun e => nomatch e)

abbrev exchangeArena : Arena where
  signature := exchangeSignature
  Law r := ∀ (q : ℕ) (h4 : 4 ∣ q) (w : Word q), r.readout () ⟨q,h4⟩ w = w

private theorem exchange_actual_law : exchangeArena.Law exchangeActual := by
  intro q h4 w
  exact exchange_involutive h4 w
private theorem exchange_rejected_law : ¬ exchangeArena.Law exchangeRejected := by
  intro h
  have hx := h 4 (by decide) (.inl (.f ⟨0,by decide⟩ (1 : Sign)))
  simp [exchangeRejected, realize, exchange, active] at hx

def exchangeRegistration : Registration exchangeArena
    (∀ (q : ℕ) (h4 : 4 ∣ q), Function.Involutive (exchange h4)) where
  actual := exchangeActual
  bridge := Iff.rfl
  variation := ⟨exchange_actual_law, exchangeRejected, exchange_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨exchangeRejected, ?_, rfl, exchange_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨4,by decide⟩, .inl (.f ⟨0,by decide⟩ (1 : Sign)),
      .inl (.f ⟨1,by decide⟩ (1 : Sign)), ?_⟩
    simp only [exchangeActual, realize]
    rw [exchange_involutive _ _, exchange_involutive _ _]
    simp

noncomputable def registration_exchange : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetNumberedHistories.TwoStep.exchange_involutive)
    (Realization exchangeSignature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetTwoStepArithmetic.exchange_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetTwoStepArithmetic.exchangeRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨exchangeArena⟩
  objectArena := .source ⟨exchangeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source exchangeArena ⟨exchangeRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize exchangeSignature
    (fun _ q w => exchange q.property (exchange q.property w)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

open _root_.D5.S3.ConceptDynamics.Coding.ResetStandardBeamGeometry
open _root_.D5.S3.ConceptDynamics.Coding.ResetFullStandardBeamRepresentation (rho)
open _root_.D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy (DimensionGroup vertex VertexModule)
open _root_.D5.S3.ConceptDynamics.Coding.ResetNativeIntegralDefect (resetNativeEquiv)

local instance nativeInt (q : ℕ) : Module ℤ (DimensionGroup (resetMatrix q)) :=
  AddCommGroup.toIntModule _

abbrev NativeParam := {q : ℕ // 0 < q ∧ 4 ∣ q}
abbrev nativeSignature : Signature where
  Params := NativeParam
  State p := ResetFullAut p.val
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := Module.End ℤ (DimensionGroup (resetMatrix p.val))
  Anchor := Empty
  finiteAnchor := inferInstance

def nativeActual : Realization nativeSignature :=
  realize nativeSignature (fun _ p f => (rho p.val p.property.1 f).toLinearMap) (fun e => nomatch e)
def nativeRejected : Realization nativeSignature :=
  realize nativeSignature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev nativeArena : Arena where
  signature := nativeSignature
  Law r := ∀ (q : ℕ) (hq : 0 < q) (h4 : 4 ∣ q),
    r.readout () ⟨q,hq,h4⟩ (aut q hq h4) =
      (LinearMap.id : Module.End ℤ (DimensionGroup (resetMatrix q))) + (resetTheta q)^2

private theorem native_actual_law : nativeArena.Law nativeActual := by
  intro q hq h4
  exact rho_eq q hq h4

private def nonzeroVertex : DimensionGroup (resetMatrix 4) :=
  (resetNativeEquiv 4 (by decide)).symm (vertex (⟨0,by decide⟩ : Fin 4) (1 : Sign))
private theorem nonzeroVertex_ne : nonzeroVertex ≠ 0 := by
  intro h
  have hz := congrArg (resetNativeEquiv 4 (by decide)) h
  simp only [nonzeroVertex, LinearEquiv.apply_symm_apply, map_zero] at hz
  have hc := congrArg (fun z : VertexModule Sign 4 => (z ⟨0,by decide⟩).coeff (1 : Sign)) hz
  norm_num [_root_.D5.S3.ConceptDynamics.Coding.InertGroupBlockConjugacy.vertex,
    MonoidAlgebra.coeff_single] at hc

private theorem native_rejected_law : ¬ nativeArena.Law nativeRejected := by
  intro h
  have hh := h 4 (by decide) (by decide)
  have he := native_actual_law 4 (by decide) (by decide)
  have hz : rho 4 (by decide) (aut 4 (by decide) (by decide)) nonzeroVertex = 0 :=
    LinearMap.congr_fun (he.trans hh.symm) nonzeroVertex
  apply nonzeroVertex_ne
  exact (rho 4 (by decide) (aut 4 (by decide) (by decide))).injective
    (hz.trans (map_zero _).symm)

def nativeRegistration : Registration nativeArena
    (∀ (q : ℕ) (hq : 0 < q) (h4 : 4 ∣ q),
      (rho q hq (aut q hq h4)).toLinearMap = LinearMap.id + (resetTheta q)^2) where
  actual := nativeActual
  bridge := Iff.rfl
  variation := ⟨native_actual_law, nativeRejected, native_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨nativeRejected, ?_, rfl, native_rejected_law⟩
      intro j hj
      exact (hj (Subsingleton.elim _ _)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨4,by decide,by decide⟩, aut 4 (by decide) (by decide), 1, ?_⟩
    intro h
    have hh := LinearMap.congr_fun h nonzeroVertex
    change rho 4 (by decide) (aut 4 (by decide) (by decide)) nonzeroVertex =
      rho 4 (by decide) 1 nonzeroVertex at hh
    rw [map_one] at hh
    change rho 4 (by decide) (aut 4 (by decide) (by decide)) nonzeroVertex = nonzeroVertex at hh
    have heq := LinearMap.congr_fun (rho_eq 4 (by decide) (by decide)) nonzeroVertex
    change rho 4 (by decide) (aut 4 (by decide) (by decide)) nonzeroVertex =
      nonzeroVertex + resetTheta 4 (resetTheta 4 nonzeroVertex) at heq
    have hadd := heq.symm.trans hh
    have hz : resetTheta 4 (resetTheta 4 nonzeroVertex) = 0 :=
      add_left_cancel (hadd.trans (add_zero _).symm)
    let f := rho 4 (by decide)
      (_root_.D5.S3.ConceptDynamics.Coding.StandardBeamHomeomorphisms.unitShift (ResetGraph 4))
    have ht := _root_.D5.S3.ConceptDynamics.Coding.ResetFullStandardBeamRepresentation.rho_unitShift
      4 (by decide)
    have hi : Function.Injective (resetTheta 4) := by
      intro a b hab
      apply f.injective
      exact (LinearMap.congr_fun ht a).trans
        (hab.trans (LinearMap.congr_fun ht b).symm)
    exact nonzeroVertex_ne (hi ((hi (hz.trans (map_zero _).symm)).trans (map_zero _).symm))

noncomputable def registration_native : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetNumberedHistories.TwoStep.rho_eq)
    (Realization nativeSignature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetTwoStepArithmetic.native_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetTwoStepArithmetic.nativeRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨nativeArena⟩
  objectArena := .source ⟨nativeArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source nativeArena ⟨nativeRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize nativeSignature (fun _ p f => (rho p.val p.property.1 f).toLinearMap) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

open _root_.D5.S3.ConceptDynamics.Coding.CountedGroupOverlap (Edge)
open _root_.D5.S3.ConceptDynamics.Coding.FixedBlockRigidity (expandedGraph)
open _root_.D5.S3.ConceptDynamics.Coding.SameCutWholeRayBridge (FiniteForgetting)

abbrev SquareState (p : NativeParam) :=
  (Edge (twoStepCarrier p.val) × Sign) × (Edge (resetMatrix p.val) × Sign) ×
    (Edge (resetMatrix p.val) × Sign) × (Edge (twoStepCarrier p.val) × Sign)
abbrev forgettingSignature : Signature where
  Params := NativeParam
  State := SquareState
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def forgettingActual : Realization forgettingSignature :=
  realize forgettingSignature (fun _ p w => (numberedData p.val p.property.1 p.property.2).squares.sq
    w.1 w.2.1 w.2.2.1 w.2.2.2) (fun e => nomatch e)
def forgettingRejected : Realization forgettingSignature :=
  realize forgettingSignature (fun _ _ _ => True) (fun e => nomatch e)

def forgettingArena : Arena where
  signature := forgettingSignature
  Law F := ∀ (q : ℕ) (hq : 0 < q) (h4 : 4 ∣ q),
    (∀ (x y y' : ℕ → Edge (resetMatrix q) × Sign)
      (r r' : ℕ → Edge (twoStepCarrier q) × Sign),
      (∀ i, i < q → F.readout () ⟨q,hq,h4⟩ (r i,x i,y i,r (i+1))) →
      (∀ i, i < q → F.readout () ⟨q,hq,h4⟩ (r' i,x i,y' i,r' (i+1))) → r 0 = r' 0) ∧
    (∀ (x x' y : ℕ → Edge (resetMatrix q) × Sign)
      (r r' : ℕ → Edge (twoStepCarrier q) × Sign),
      (∀ i, i < q → F.readout () ⟨q,hq,h4⟩ (r i,x i,y i,r (i+1))) →
      (∀ i, i < q → F.readout () ⟨q,hq,h4⟩ (r' i,x' i,y i,r' (i+1))) → r q = r' q)

private theorem forgetting_actual_law : forgettingArena.Law forgettingActual := by
  intro q hq h4
  exact ⟨(finiteForgetting q hq h4).left, (finiteForgetting q hq h4).right⟩

private theorem forgetting_rejected_law : ¬ forgettingArena.Law forgettingRejected := by
  intro h
  let e := Alternating.originalEdge (by decide : 0 < 4) (.f ⟨0,by decide⟩ (1 : Sign))
  let d := numberedBoundaryEquiv (by decide : 0 < 4) (.d ⟨0,by decide⟩ (1 : Sign))
  let f := numberedBoundaryEquiv (by decide : 0 < 4) (.ff ⟨0,by decide⟩ (1 : Sign))
  have hh := (h 4 (by decide) (by decide)).1 (fun _ => e) (fun _ => e) (fun _ => e)
    (fun _ => d) (fun _ => f) (fun _ _ => trivial) (fun _ _ => trivial)
  have hu := (numberedBoundaryEquiv (by decide : 0 < 4)).injective hh
  cases hu

private def validSquare : SquareState (⟨4,by decide,by decide⟩ : NativeParam) :=
  (numberedBoundaryEquiv (by decide) (.aa ⟨0,by decide⟩ (1 : Sign) (by decide)),
    Alternating.originalEdge (by decide) (.f ⟨0,by decide⟩ (1 : Sign)),
    Alternating.originalEdge (by decide) (.f ⟨2,by decide⟩ (1 : Sign)),
    numberedBoundaryEquiv (by decide) (.d ⟨0,by decide⟩ (Multiplicative.ofAdd true : Sign)))
private def invalidSquare : SquareState (⟨4,by decide,by decide⟩ : NativeParam) :=
  (validSquare.1, validSquare.2.1,
    Alternating.originalEdge (by decide) (.f ⟨1,by decide⟩ (1 : Sign)), validSquare.2.2.2)

private theorem validSquare_law : forgettingActual.readout () ⟨4,by decide,by decide⟩ validSquare := by
  simpa only [validSquare, numberedData, Equiv.symm_apply_apply,
    Alternating.actualEdgeEquiv, Alternating.typed_original, forgettingActual, realize,
    next2, Alternating.zero, Alternating.flipSign, one_mul] using
    (Square.fdSwap (hq := by decide) (⟨0,by decide⟩ : Fin 4) (1 : Sign)
      (by decide) (Or.inl rfl))

private theorem invalidSquare_not : ¬ forgettingActual.readout () ⟨4,by decide,by decide⟩ invalidSquare := by
  intro h
  have he := (numberedData 4 (by decide) (by decide)).squares.endpoints h
  have ha := he.2.1
  have hh := congrArg (fun v : Fin 4 × Sign => v.1.val) ha
  change (2 : ℕ) = 1 at hh
  omega

def forgettingRegistration : Registration forgettingArena
    (∀ (q : ℕ) (hq : 0 < q) (h4 : 4 ∣ q), FiniteForgetting (numberedData q hq h4).squares q) where
  actual := forgettingActual
  bridge := by
    constructor
    · intro h q hq h4
      exact ⟨(h q hq h4).left, (h q hq h4).right⟩
    · intro h q hq h4
      exact ⟨hq,(h q hq h4).1,(h q hq h4).2⟩
  variation := ⟨forgetting_actual_law, forgettingRejected, forgetting_rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨forgettingRejected, ?_, rfl, forgetting_rejected_law⟩
      intro j hj
      have he : j = i := by
        change Unit at i j
        exact @Subsingleton.elim Unit inferInstance j i
      exact (hj he).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨4,by decide,by decide⟩,validSquare,invalidSquare,?_⟩
    intro h
    apply invalidSquare_not
    exact Eq.mp h validSquare_law

noncomputable def registration_forgetting : Contract.Registration.{_,_,_,0,0,0,0,0,0,0,0,0}
    (@_root_.D5.S3.ConceptDynamics.Coding.ResetNumberedHistories.TwoStep.finiteForgetting)
    (Realization forgettingSignature) Unit Unit := {
  unitName := `Reg.D5.S3.ConceptDynamics.Coding.ResetTwoStepArithmetic.forgetting_unit
  realizationName := `Reg.D5.S3.ConceptDynamics.Coding.ResetTwoStepArithmetic.forgettingRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨forgettingArena⟩
  objectArena := .source ⟨forgettingArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source forgettingArena ⟨forgettingRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize forgettingSignature
    (fun _ p w => (numberedData p.val p.property.1 p.property.2).squares.sq
      w.1 w.2.1 w.2.2.1 w.2.2.2) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[] }

end
end Reg.D5.S3.ConceptDynamics.Coding.ResetTwoStepArithmetic
