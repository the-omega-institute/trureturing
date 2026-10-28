import D5.S3.Quantum.Matrix.HsfProjectionCubic
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Dependent-family registrations for the projection certificate and actual derivative bounds. -/

open _root_.D5.S3.Quantum.Matrix.HsfProjectionCubic
open _root_.D5.S3.Quantum.Matrix.HsfQubitMixedCubic
open _root_.D5.S3.Quantum.Matrix.HsfIdentityCubicDerivatives
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Reg.D5.S3.Quantum.Matrix.HsfProjectionCubic
noncomputable section
open Classical
universe u

private structure MatrixScope where
  index : Type u
  finiteIndex : Fintype index
  decidableIndex : DecidableEq index
attribute [instance] MatrixScope.finiteIndex MatrixScope.decidableIndex

private abbrev signature : Signature where
  Params := MatrixScope.{u}
  State s := Matrix s.index s.index ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := Bool
  Anchor := Empty
  finiteAnchor := inferInstance

private def hermitianActual : Realization signature :=
  realize signature (fun _ _ M => decide M.IsHermitian) (fun e => nomatch e)
private def positiveActual : Realization signature :=
  realize signature (fun _ _ M => decide M.PosSemidef) (fun e => nomatch e)
private def rejected : Realization signature :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)

private theorem hermitianDependence : ObservationalDependence signature.{u} hermitianActual := by
  intro i
  let s : MatrixScope.{u} := ⟨ULift.{u} Unit, inferInstance, inferInstance⟩
  refine ⟨s, 0, Complex.I • (1 : Matrix s.index s.index ℂ), ?_⟩
  have hn : ¬ (Complex.I • (1 : Matrix s.index s.index ℂ)).IsHermitian := by
    intro h
    have he := congrArg (fun M : Matrix s.index s.index ℂ => (M ⟨()⟩ ⟨()⟩).im) h.eq
    norm_num at he
  simp [hermitianActual, realize, hn]

private theorem positiveDependence : ObservationalDependence signature.{u} positiveActual := by
  intro i
  let s : MatrixScope.{u} := ⟨ULift.{u} Unit, inferInstance, inferInstance⟩
  refine ⟨s, 0, (-1 : Matrix s.index s.index ℂ), ?_⟩
  have hn : ¬ (-1 : Matrix s.index s.index ℂ).PosSemidef := by
    intro h
    have he := h.diag_nonneg (i := ⟨()⟩)
    norm_num at he
  simp [positiveActual, realize, hn, Matrix.PosSemidef.zero]

namespace Certificate
private abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] (H G P : Matrix n n ℂ),
    R.readout () ⟨n, inferInstance, inferInstance⟩ H = true →
    G.IsHermitian → P.IsHermitian → P*P = P →
    27*(coefficient2 (H+G) H P-3*coefficient3 (H+G) H P) = projectionSOS H G P
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hh := h (n := ULift.{u} Unit) (Complex.I • 1) 1 0 rfl
    Matrix.isHermitian_one Matrix.isHermitian_zero (by simp)
  norm_num [coefficient2, coefficient3, traceCoefficient2, traceCoefficient3,
    projectionSOS, traceLocalizer, Matrix.trace, Matrix.mul_apply, Fintype.sum_unique,
    Complex.ext_iff] at hh

def evidence : Registration arena.{u} (type_of% (@projection_certificate.{u})) where
  actual := hermitianActual.{u}
  bridge := by
    constructor
    · intro source n _ _ X H P hp hq hr hs
      exact source X H P (of_decide_eq_true hp) hq hr hs
    · intro law n _ _ X H P hp hq hr hs
      exact law X H P (decide_eq_true hp) hq hr hs
  variation := ⟨by
    intro n _ _ X H P hp hq hr hs
    exact projection_certificate X H P (of_decide_eq_true hp) hq hr hs,
    rejected.{u}, rejected_law.{u}⟩
  sensitivity := ⟨fun i => ⟨rejected.{u},
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law.{u}⟩,
    fun e => nomatch e⟩
  dependence := hermitianDependence.{u}

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@projection_certificate.{u}) (Realization signature.{u})
    (type_of% (@_root_.Matrix.{u,u,0})) Unit := {
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfProjectionCubic.Certificate.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfProjectionCubic.Certificate.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} hermitianActual.{u}.readout hermitianActual.{u}.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.HsfProjectionCubic
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
end Certificate

namespace Projection
private abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] (X H P : Matrix n n ℂ),
    R.readout () ⟨n, inferInstance, inferInstance⟩ H = true →
    (X-H).PosSemidef → P.IsHermitian → P*P = P →
    let g := fun t : ℝ => (Matrix.trace
      ((CFC.rpow (1+t • P) (-(1 : ℝ)/3) * (X+t • H) *
        CFC.rpow (1+t • P) (-(1 : ℝ)/3))^3)).re
    iteratedDeriv 3 g 0 ≤ iteratedDeriv 2 g 0
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hg : ((-1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ)-(-2)).PosSemidef := by
    rw [show (-1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ)-(-2) = 1 by norm_num]
    exact Matrix.PosSemidef.one
  have hh := h (n := ULift.{u} Unit) (-1) (-2) 1 rfl hg Matrix.isHermitian_one (by simp)
  obtain ⟨hd2, hd3⟩ := identity_cubic_trace_derivatives
    (-1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) (-2) 1 Matrix.isHermitian_one
  dsimp only at hh hd2 hd3
  rw [hd2, hd3] at hh
  norm_num [coefficient2, coefficient3, traceCoefficient2, traceCoefficient3,
    Matrix.trace, Matrix.mul_apply, Matrix.ofNat_apply, Matrix.natCast_apply,
    Fintype.sum_unique] at hh

def evidence : Registration arena.{u} (type_of% (@projection_cubic_compatibility.{u})) where
  actual := positiveActual.{u}
  bridge := by
    constructor
    · intro source n _ _ X H P hp hq hr hs
      exact source X H P (of_decide_eq_true hp) hq hr hs
    · intro law n _ _ X H P hp hq hr hs
      exact law X H P (decide_eq_true hp) hq hr hs
  variation := ⟨by
    intro n _ _ X H P hp hq hr hs
    exact projection_cubic_compatibility X H P (of_decide_eq_true hp) hq hr hs,
    rejected.{u}, rejected_law.{u}⟩
  sensitivity := ⟨fun i => ⟨rejected.{u},
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law.{u}⟩,
    fun e => nomatch e⟩
  dependence := positiveDependence.{u}

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@projection_cubic_compatibility.{u}) (Realization signature.{u})
    (type_of% (@_root_.Matrix.{u,u,0})) Unit := {
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfProjectionCubic.Projection.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfProjectionCubic.Projection.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} positiveActual.{u}.readout positiveActual.{u}.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.HsfProjectionCubic
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
end Projection

namespace Involution
private abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [Fintype n] [DecidableEq n] (X A J : Matrix n n ℂ),
    R.readout () ⟨n, inferInstance, inferInstance⟩ (X+A) = true →
    (X-A).PosSemidef → J.IsHermitian → J*J = 1 →
    let f : ℝ → ℝ := fun t : ℝ => (Matrix.trace
      ((CFC.rpow (1+t • J) (-(1 : ℝ)/3) * (X+t • A) *
        CFC.rpow (1+t • J) (-(1 : ℝ)/3))^3)).re
    0 ≤ iteratedDeriv 2 f 0 ∧ |iteratedDeriv 3 f 0| ≤ 5*iteratedDeriv 2 f 0
private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hg : ((-1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ)-(-2)).PosSemidef := by
    rw [show (-1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ)-(-2) = 1 by norm_num]
    exact Matrix.PosSemidef.one
  have hh := h (n := ULift.{u} Unit) (-1) (-2) 1 rfl hg Matrix.isHermitian_one (by simp)
  obtain ⟨hd2, hd3⟩ := identity_cubic_trace_derivatives
    (-1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) (-2) 1 Matrix.isHermitian_one
  dsimp only at hh hd2 hd3
  rw [hd2, hd3] at hh
  norm_num [coefficient2, coefficient3, traceCoefficient2, traceCoefficient3,
    Matrix.trace, Matrix.mul_apply, Matrix.ofNat_apply, Matrix.natCast_apply,
    Fintype.sum_unique] at hh

def evidence : Registration arena.{u} (type_of% (@involution_cubic_compatibility.{u})) where
  actual := positiveActual.{u}
  bridge := by
    constructor
    · intro source n _ _ X H P hp hq hr hs
      exact source X H P (of_decide_eq_true hp) hq hr hs
    · intro law n _ _ X H P hp hq hr hs
      exact law X H P (decide_eq_true hp) hq hr hs
  variation := ⟨by
    intro n _ _ X H P hp hq hr hs
    exact involution_cubic_compatibility X H P (of_decide_eq_true hp) hq hr hs,
    rejected.{u}, rejected_law.{u}⟩
  sensitivity := ⟨fun i => ⟨rejected.{u},
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law.{u}⟩,
    fun e => nomatch e⟩
  dependence := positiveDependence.{u}

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@involution_cubic_compatibility.{u}) (Realization signature.{u})
    (type_of% (@_root_.Matrix.{u,u,0})) Unit := {
  unitName := `Reg.D5.S3.Quantum.Matrix.HsfProjectionCubic.Involution.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.HsfProjectionCubic.Involution.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨evidence.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} positiveActual.{u}.readout positiveActual.{u}.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.HsfProjectionCubic
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
end Involution

end
end Reg.D5.S3.Quantum.Matrix.HsfProjectionCubic
