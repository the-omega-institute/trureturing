import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Recovery.PetzExponentialBoundaryEvaluation
import Reg.Support.SingleDependentReadout

/-! Source-bound observations of the boundary and Gram trace estimates. -/

noncomputable section

open PetzExponentialBoundaryEvaluation
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Matrix MeasureTheory
open _root_.D5.S3.Quantum.Foundation.FiniteTraceDistance
open scoped Matrix.Norms.Frobenius

namespace Reg.D5.S3.Quantum.Recovery.PetzExponentialBoundaryEvaluation

universe u v w x y

abbrev boundSignature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ → Prop)

def boundActual : Realization boundSignature :=
  realize boundSignature (fun _ _ a b => a ≤ b) (fun e => nomatch e)

def boundRejected : Realization boundSignature :=
  realize boundSignature (fun _ _ _ _ => False) (fun e => nomatch e)

private theorem boundDependence : ObservationalDependence boundSignature boundActual := by
  intro role
  refine ⟨(), 0, 1, ?_⟩
  intro heq
  have h := congrFun heq 0
  norm_num [boundActual, realize] at h

abbrev blocksArena : Arena where
  signature := boundSignature
  Law R := ∀ {β : Type u} [Fintype β] {ν : β → Type v} [∀ b, Fintype (ν b)]
    {H : β → Type w} [∀ b, NormedAddCommGroup (H b)] [∀ b, InnerProductSpace ℂ (H b)]
    (ω : (b : β) → ν b → ℝ) (a : (b : β) → ν b → H b) (m : ℕ)
    (_hm : ∀ b, (distinctFrequencies (ω b)).card ≤ m),
    Integrable (fun s : ℝ => petzWeight s * ‖blockCurve ω a s‖ ^ 2) ∧
    R.readout () () (‖blockCurve ω a 0‖ ^ 2)
      ((2 * (m : ℝ)) * (∫ s : ℝ, petzWeight s * ‖blockCurve ω a s‖ ^ 2))

private theorem blocksRejectedLaw : ¬ blocksArena.{u, v, w}.Law boundRejected := by
  intro law
  exact (law (β := ULift.{u} (Fin 0)) (ν := fun _ => ULift.{v} Unit)
    (H := fun _ => EuclideanSpace ℂ (ULift.{w} Unit))
    (fun _ _ => 0) (fun _ _ => 0) 0 (fun b => isEmptyElim b)).2

def blocksFamily : Registration blocksArena.{u, v, w} (type_of% @weighted_evaluation_blocks.{u, v, w}) where
  actual := boundActual
  bridge := Iff.rfl
  variation := ⟨@weighted_evaluation_blocks.{u, v, w}, boundRejected, blocksRejectedLaw.{u, v, w}⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    blocksArena.{u, v, w}.Law boundActual boundRejected blocksRejectedLaw.{u, v, w}
  dependence := boundDependence

def blocksAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weighted_evaluation_blocks.{u, v, w}) (Realization boundSignature) Unit Unit where
  unitName := `PetzExponentialBoundaryEvaluation.weighted_evaluation_blocks.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzExponentialBoundaryEvaluation.blocksFamily
  realizationSource := none
  generated := false
  arena := .source ⟨blocksArena.{u, v, w}⟩
  objectArena := .source ⟨blocksArena.{u, v, w}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source blocksArena.{u, v, w} ⟨blocksFamily.{u, v, w}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize boundSignature (fun _ _ a b => a ≤ b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.PetzExponentialBoundaryEvaluation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev modularArena : Arena where
  signature := boundSignature
  Law R := ∀ {r : Type u} {c : Type v} {β : Type w} {P : Type x} {Q : Type y}
    [Fintype r] [Fintype c] [Finite β] [Fintype P] [Fintype Q]
    (block : r → c → β) (outer : β → ℝ) (q : Q → ℝ) (p : P → ℝ)
    (A : Matrix r c ℂ) (C : Q × P → Matrix r c ℂ) (m : ℕ)
    (_hm : ∀ b, (distinctFrequencies (retainedFrequency (outer b) q p)).card ≤ m),
    Integrable (fun s : ℝ => petzWeight s * ‖petzBoundary block outer q p A C s‖ ^ 2) ∧
    R.readout () () (‖petzBoundary block outer q p A C 0‖ ^ 2)
      ((2 * (m : ℝ)) * (∫ s : ℝ, petzWeight s * ‖petzBoundary block outer q p A C s‖ ^ 2))

private theorem modularRejectedLaw : ¬ modularArena.{u, v, w, x, y}.Law boundRejected := by
  intro law
  exact (law (r := ULift.{u} (Fin 0)) (c := ULift.{v} Unit) (β := ULift.{w} (Fin 0))
    (P := ULift.{x} Unit) (Q := ULift.{y} Unit) (fun i _ => isEmptyElim i)
    (fun _ => 1) (fun _ => 1) (fun _ => 1) 0 (fun _ => 0) 0 (fun b => isEmptyElim b)).2

def modularFamily : Registration modularArena.{u, v, w, x, y} (type_of% @weighted_evaluation_petz_boundary.{u, v, w, x, y}) where
  actual := boundActual
  bridge := Iff.rfl
  variation := ⟨@weighted_evaluation_petz_boundary.{u, v, w, x, y}, boundRejected, modularRejectedLaw.{u, v, w, x, y}⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    modularArena.{u, v, w, x, y}.Law boundActual boundRejected modularRejectedLaw.{u, v, w, x, y}
  dependence := boundDependence

def modularAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weighted_evaluation_petz_boundary.{u, v, w, x, y}) (Realization boundSignature) Unit Unit where
  unitName := `PetzExponentialBoundaryEvaluation.weighted_evaluation_petz_boundary.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzExponentialBoundaryEvaluation.modularFamily
  realizationSource := none
  generated := false
  arena := .source ⟨modularArena.{u, v, w, x, y}⟩
  objectArena := .source ⟨modularArena.{u, v, w, x, y}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source modularArena.{u, v, w, x, y} ⟨modularFamily.{u, v, w, x, y}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize boundSignature (fun _ _ a b => a ≤ b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.PetzExponentialBoundaryEvaluation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "arg", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

abbrev traceArena : Arena where
  signature := boundSignature
  Law R := ∀ {r : Type u} {c : Type v} [Fintype r] [Fintype c]
    {β : Type w} {P : Type x} {Q : Type y} [Finite β] [Fintype P] [Fintype Q]
    (block : r → c → β) (outer : β → ℝ) (q : Q → ℝ) (p : P → ℝ)
    (A : Matrix r c ℂ) (C : Q × P → Matrix r c ℂ) (m : ℕ)
    (_hm : ∀ b, (distinctFrequencies (retainedFrequency (outer b) q p)).card ≤ m)
    (_hA : ‖A‖ = 1) (_hB : ‖A - petzBoundary block outer q p A C 0‖ = 1),
    let B := A - petzBoundary block outer q p A C 0
    R.readout () () (traceNorm (B * Bᴴ - A * Aᴴ) ^ 2)
      ((8 * (m : ℝ)) * (∫ s : ℝ, petzWeight s * ‖petzBoundary block outer q p A C s‖ ^ 2))

private theorem traceRejectedLaw : ¬ traceArena.{u, v, w, x, y}.Law boundRejected := by
  classical
  intro law
  let A : Matrix (ULift.{u} Unit) (ULift.{v} Unit) ℂ := Matrix.of fun _ _ => 1
  let block (_ : ULift.{u} Unit) (_ : ULift.{v} Unit) : ULift.{w} Unit := ⟨()⟩
  let q (_ : ULift.{y} Unit) : ℝ := 1
  let p (_ : ULift.{x} Unit) : ℝ := 1
  have hA : ‖A‖ = 1 := by simp [Matrix.frobenius_norm_def, A]
  have hE : petzBoundary block (fun _ => 1) q p A (fun _ => A) 0 = 0 := by
    ext i j
    simp [petzBoundary, A, p, q]
  have hm (b : ULift.{w} Unit) :
      (distinctFrequencies (retainedFrequency 1 q p)).card ≤ 2 := by
    unfold distinctFrequencies
    exact Finset.card_image_le.trans (by simp)
  exact law block (fun _ => 1) q p A (fun _ => A) 2 hm hA (by rwa [hE, sub_zero])

def traceFamily : Registration traceArena.{u, v, w, x, y} (type_of% @traceNorm_gram_sub_sq_le_petz_boundary.{u, v, w, x, y}) where
  actual := boundActual
  bridge := Iff.rfl
  variation := ⟨@traceNorm_gram_sub_sq_le_petz_boundary.{u, v, w, x, y}, boundRejected, traceRejectedLaw.{u, v, w, x, y}⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    traceArena.{u, v, w, x, y}.Law boundActual boundRejected traceRejectedLaw.{u, v, w, x, y}
  dependence := boundDependence

def traceAudit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@traceNorm_gram_sub_sq_le_petz_boundary.{u, v, w, x, y}) (Realization boundSignature) Unit Unit where
  unitName := `PetzExponentialBoundaryEvaluation.traceNorm_gram_sub_sq_le_petz_boundary.__information_unit
  realizationName := `Reg.D5.S3.Quantum.Recovery.PetzExponentialBoundaryEvaluation.traceFamily
  realizationSource := none
  generated := false
  arena := .source ⟨traceArena.{u, v, w, x, y}⟩
  objectArena := .source ⟨traceArena.{u, v, w, x, y}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source traceArena.{u, v, w, x, y} ⟨traceFamily.{u, v, w, x, y}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize boundSignature (fun _ _ a b => a ≤ b) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Recovery.PetzExponentialBoundaryEvaluation
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Quantum.Recovery.PetzExponentialBoundaryEvaluation
