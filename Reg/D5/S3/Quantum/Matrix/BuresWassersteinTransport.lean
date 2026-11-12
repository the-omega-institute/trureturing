import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout
import D5.S3.Quantum.Matrix.BuresWassersteinTransport

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Matrix.BuresWassersteinTransport
open _root_.D5.S3.Quantum.Matrix.HwangKimNearOrderRefutation
open LeanInformationAudit Matrix
open scoped MatrixOrder ComplexOrder

namespace Reg.D5.S3.Quantum.Matrix.BuresWassersteinTransport
noncomputable section
open Classical

abbrev Mat (m : ℕ) := Matrix (Fin m) (Fin m) ℂ
abbrev Params := ℕ
abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature Params
    (fun m => Mat m) (fun _ => Bool)

def actual : Realization signature :=
  realize signature (fun _ _ Z => decide (Z = 1)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => true) (fun e => nomatch e)

abbrev conclusion {m n : ℕ} (w : Fin n → ℝ) (A : Fin n → Mat m) (W : Mat m) :=
  (∀ X : Mat m, X.PosDef →
    (∑ j, w j * buresWassersteinDistance W (A j)^2) ≤
      ∑ j, w j * buresWassersteinDistance X (A j)^2) ∧
  (∀ X : Mat m, X.PosDef →
    (((∑ j, w j * buresWassersteinDistance X (A j)^2) ≤
      ∑ j, w j * buresWassersteinDistance W (A j)^2) ↔ X = W)) ∧
  wassersteinBarycenter w A = W

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m n : ℕ} (w : Fin n → ℝ) (A T : Fin n → Mat m) {W : Mat m},
    (∀ j, 0 < w j) → (∑ j, w j) = 1 → (∀ j, (A j).PosDef) →
    W.PosDef → (∀ j, (T j).PosDef) → (∀ j, T j * W * T j = A j) →
    R.readout () m (∑ j, w j • T j) = true → conclusion w A W

private theorem rejected_law : ¬ arena.Law rejected := by
  intro law
  let K : Mat 1 := (2 : ℝ) • 1
  let A : Mat 1 := (4 : ℝ) • 1
  have hK : K.PosDef := Matrix.PosDef.one.smul (by norm_num)
  have hA : A.PosDef := Matrix.PosDef.one.smul (by norm_num)
  have htrans : K * 1 * K = A := by
    dsimp [K, A]
    simp only [mul_one, smul_mul_assoc, Matrix.mul_smul, one_mul, smul_smul]
    norm_num
  have hx := law (fun _ : Fin 1 => (1 : ℝ)) (fun _ => A) (fun _ => K)
    (W := 1) (by intro j; norm_num) (by simp)
    (fun _ => hA) Matrix.PosDef.one (fun _ => hK) (fun _ => htrans) rfl
  have hy := law (fun _ : Fin 1 => (1 : ℝ)) (fun _ => A) (fun _ => 1)
    (W := A) (by intro j; norm_num) (by simp)
    (fun _ => hA) hA (fun _ => Matrix.PosDef.one) (by intro j; simp) rfl
  have he : (1 : Mat 1) = A := hx.2.2.symm.trans hy.2.2
  have := congrArg (fun Z : Mat 1 => Z 0 0) he
  norm_num [A, Matrix.one_apply] at this

private theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨1, 1, 0, ?_⟩
  simp [actual, realize]

def evidence : Registration arena (type_of% (@finite_barycenter_of_dual)) where
  actual := actual
  bridge := by
    constructor
    · intro source m n w A T W hw hws hA hW hT ht hb
      exact source w A T hw hws hA hW hT ht (of_decide_eq_true hb)
    · intro law m n w A T W hw hws hA hW hT ht hb
      exact law w A T hw hws hA hW hT ht (decide_eq_true hb)
  variation := ⟨by
    intro m n w A T W hw hws hA hW hT ht hb
    exact finite_barycenter_of_dual w A T hw hws hA hW hT ht (of_decide_eq_true hb),
    rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

def registration :
    Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
      (@_root_.D5.S3.Quantum.Matrix.BuresWassersteinTransport.finite_barycenter_of_dual)
      (Realization signature) Unit Unit := {
  unitName := `Reg.D5.S3.Quantum.Matrix.BuresWassersteinTransport.unit
  realizationName := `Reg.D5.S3.Quantum.Matrix.BuresWassersteinTransport.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Matrix.BuresWassersteinTransport
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body",
        "body","body","body","body","domain"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn","arg"]
      booleanPredicate := true }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms evidence
#print axioms registration
end
end Reg.D5.S3.Quantum.Matrix.BuresWassersteinTransport

/- Unfinished registration audit, tracked with the complete source return:
https://github.com/the-omega-institute/trureturing/issues/29594
The faithful source-equivalence, actual law, rejected-law variation,
whole-family sensitivity and observational dependence all compile.
The current inspector reports declared_unresolved, IE-C050 ClosedTruthReadout,
unclassified_form / source.unlinked_operand, Classical.choice;
source_operand=Classical.choice. This is not declared_validated and does not
waive kernel, sorry, axiom, source fidelity, freeze or other required checks.
-/
