import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.TimeArrow.NativeJointExterior
import Reg.Support.DependentFamily
import Reg.Support.SingleDependentReadout

/-! Typed parity observation for the complete native marked exterior law. -/

open scoped BigOperators
open Finset LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open _root_.D5.S3.Estimation.TimeArrow.NativeJointExterior
open private chainWeight leftFiber rightFiber cylinderMass_eq from
  D5.S3.Estimation.TimeArrow.NativeJointExterior

noncomputable section
namespace Reg.D5.S3.Estimation.TimeArrow.NativeJointExterior

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature ℕ Vertex (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ M y => chi (M := M) y) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {M q a b : ℕ} {r : ℝ}
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (S : Support M q)
    (l : Fin (a - 1) → Vertex M) (v : Fin (b - 1) → Vertex M)
    (i : Fin M) (hi : i ∈ S.val) (σ : ℝ) (hσ : σ = 1 ∨ σ = -1),
    (∑ y : Vertex M, if R.readout () M y = σ then cylinderMass r S l v (.inl i) y else 0) =
      ((1 + σ * r)/(2 * (2 * (M : ℝ)))) *
        (∑ z : Vertex M, ∑ w : Vertex M, cylinderMass r S l v z w)

def family : Registration arena (type_of% (@native_marked_joint_exterior)) := by
  have hbad : ¬ arena.Law rejected := by
    classical
    intro h
    let S : Support 2 1 := ⟨{0}, by simp⟩
    let e : Fin 0 → Vertex 2 := Fin.elim0
    have ht := h (M := 2) (q := 1) (a := 0) (b := 0) (r := (1/2:ℝ))
      (by omega) (by omega) (by norm_num) (by norm_num)
      (by norm_num [compensation]) S e e 0 (by simp [S]) 1 (Or.inl rfl)
    have hf (x y : Vertex 2) :
        cylinderMass (a := 0) (b := 0) (1/2:ℝ) S e e x y =
          (1/4:ℝ) * transition (1/2:ℝ) S x y := by
      rw [cylinderMass_eq]
      simp [leftFiber, rightFiber, chainWeight, e]
    have hrw := (finite_support_bayes (s := 0) (M := 2) (q := 1) (r := (1/2:ℝ))
      (by omega) (by omega) (by norm_num) (by norm_num)
      (by norm_num [compensation]) (by norm_num [compensation]) .path).1 S |>.1.2
    simp only [rejected, realize, zero_ne_one, ite_false, sum_const_zero] at ht
    simp_rw [hf, ← mul_sum, hrw] at ht
    norm_num [Fintype.card_sum, Fintype.card_fin] at ht
  exact {
    actual := actual
    bridge := Iff.rfl
    variation := ⟨@native_marked_joint_exterior, rejected, hbad⟩
    sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
      arena.Law actual rejected hbad
    dependence := by
      intro _
      change ∃ (p : ℕ) (x y : Vertex p), chi x ≠ chi y
      refine ⟨1, Sum.inl 0, Sum.inr 0, ?_⟩
      norm_num [chi] }

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_marked_joint_exterior)
    (type_of% (realize signature (fun _ M y => chi (M := M) y) (fun e => nomatch e)))
    (ℕ → Type) Unit where
  unitName := `D5.S3.Estimation.TimeArrow.NativeJointExterior.native_marked_joint_exterior.__information_unit
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.NativeJointExterior.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ M y => chi (M := M) y) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some Vertex
  sourceSelection := some {
    owner := `D5.S3.Estimation.TimeArrow.NativeJointExterior
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "arg", "body", "fn", "fn", "fn", "arg", "fn", "arg", "fn"]
      stateBinder := 17
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms registration
end Reg.D5.S3.Estimation.TimeArrow.NativeJointExterior
