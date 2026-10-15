import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Dynamics.FinitePropagationHistory
import Reg.Support.DependentFamily

open LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Dynamics.FinitePropagationHistory
noncomputable section
universe u
namespace Reg.D5.S3.Quantum.Dynamics.FinitePropagationHistory

abbrev signature : Signature where
  Params := Σ H : Type u, Σ ng : NormedAddCommGroup H,
    letI := ng; InnerProductSpace ℂ H × ℕ
  State p :=
    letI := p.2.1
    letI := p.2.2.1
    Submodule ℂ (ClockHistory p.1 p.2.2.2)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p :=
    letI := p.2.1
    letI := p.2.2.1
    Submodule ℂ (ClockHistory p.1 p.2.2.2) → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ _ x y => x = y) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law R := ∀ {H : Type u} [ng : NormedAddCommGroup H] [ip : InnerProductSpace ℂ H]
    (U : ℕ → H ≃ₗᵢ[ℂ] H) (T : ℕ),
    R.readout () ⟨H, ng, ip, T⟩
      (LinearMap.range (historyEmbedding U T).toLinearMap) (propagation U T).ker

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  exact h (fun _ => LinearIsometryEquiv.refl ℂ (EuclideanSpace ℂ (ULift.{u} Unit))) 0

private theorem dependence : ObservationalDependence signature.{u} actual := by
  intro i
  let p : signature.{u}.Params := ⟨EuclideanSpace ℂ (ULift.{u} Unit), inferInstance, inferInstance, 0⟩
  refine ⟨p, ⊥, ⊤, ?_⟩
  intro h
  have he := congrFun h ⊥
  have hbot : (⊥ : Submodule ℂ (ClockHistory (EuclideanSpace ℂ (ULift.{u} Unit)) 0)) = ⊤ := by
    have : (⊤ : Submodule ℂ (ClockHistory (EuclideanSpace ℂ (ULift.{u} Unit)) 0)) = ⊥ :=
      he.mp rfl
    exact this.symm
  exact bot_ne_top hbot

def family : Registration arena.{u} (type_of% (@history_range.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@history_range, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, rejected_law⟩,
    fun e => nomatch e⟩
  dependence := dependence

def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@history_range.{u})
    (type_of% (realize signature.{u} (fun _ _ x y => x = y) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S3.Quantum.Dynamics.FinitePropagationHistory.history_range.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.FinitePropagationHistory.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.FinitePropagationHistory
    definition := none
    coordinates := #[0, 1, 2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

abbrev kernelSignature : Signature where
  Params := Σ H : Type u, Σ ng : NormedAddCommGroup H,
    letI := ng; InnerProductSpace ℂ H × ℕ
  State p :=
    letI := p.2.1
    ClockHistory p.1 p.2.2.2
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p :=
    letI := p.2.1
    ClockHistory p.1 p.2.2.2 → Prop
  Anchor := Empty
  finiteAnchor := inferInstance

def kernelActual : Realization kernelSignature.{u} :=
  realize kernelSignature (fun _ _ x y => x = y) (fun e => nomatch e)

def kernelRejected : Realization kernelSignature.{u} :=
  realize kernelSignature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev kernelArena : Arena where
  signature := kernelSignature.{u}
  Law R := ∀ {H : Type u} [ng : NormedAddCommGroup H] [ip : InnerProductSpace ℂ H]
    (U : ℕ → H ≃ₗᵢ[ℂ] H) (T : ℕ) (x : ClockHistory H T),
    propagation U T x = 0 ↔
      R.readout () ⟨H, ng, ip, T⟩ x (trajectory U T (x 0))

private theorem kernel_rejected_law : ¬ kernelArena.{u}.Law kernelRejected := by
  intro h
  exact (h (fun _ => LinearIsometryEquiv.refl ℂ (EuclideanSpace ℂ (ULift.{u} Unit))) 0 0).mp (map_zero _)

private theorem kernel_dependence : ObservationalDependence kernelSignature.{u} kernelActual := by
  intro i
  let p : kernelSignature.{u}.Params := ⟨EuclideanSpace ℂ (ULift.{u} Unit), inferInstance, inferInstance, 0⟩
  let y : ClockHistory (EuclideanSpace ℂ (ULift.{u} Unit)) 0 := WithLp.toLp 2 (fun _ => WithLp.toLp 2 (fun _ => (1 : ℂ)))
  refine ⟨p, 0, y, ?_⟩
  intro h
  have he := congrFun h 0
  have hy : y = 0 := he.mp rfl
  have hz := congrArg (fun z : ClockHistory (EuclideanSpace ℂ (ULift.{u} Unit)) 0 => (z 0) (ULift.up ())) hy
  simpa [y] using hz

def kernelFamily : Registration kernelArena.{u} (type_of% (@propagation_kernel.{u})) where
  actual := kernelActual
  bridge := Iff.rfl
  variation := ⟨@propagation_kernel, kernelRejected, kernel_rejected_law⟩
  sensitivity := ⟨fun i => ⟨kernelRejected,
    fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, kernel_rejected_law⟩,
    fun e => nomatch e⟩
  dependence := kernel_dependence

def kernelRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@propagation_kernel.{u})
    (type_of% (realize kernelSignature.{u} (fun _ _ x y => x = y) (fun e => nomatch e)))
    Unit Unit := {
  unitName := `D5.S3.Quantum.Dynamics.FinitePropagationHistory.propagation_kernel.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Dynamics.FinitePropagationHistory.kernelFamily
  realizationSource := none
  generated := false
  arena := .source ⟨kernelArena⟩
  objectArena := .source ⟨kernelArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source kernelArena ⟨kernelFamily⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize kernelSignature (fun _ _ x y => x = y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Dynamics.FinitePropagationHistory
    definition := none
    coordinates := #[0, 1, 2, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms family
#print axioms registration
#print axioms kernelFamily
#print axioms kernelRegistration
end Reg.D5.S3.Quantum.Dynamics.FinitePropagationHistory
