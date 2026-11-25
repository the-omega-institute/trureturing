import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.WordMean
import Reg.Support.DependentFamily

/-! The trace of the balanced product in the four-copy near-scalar lower bound. -/

namespace Reg.D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.WordMean

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Quantum.Analysis.RefinedBMVNearScalarWordMean (wordMean_sub_balanced_ge)
open _root_.RefinedBMV (balancedWords evalWord)
open LeanInformationAudit Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.Frobenius

noncomputable section

universe u

abbrev signature : Signature where
  Params := Σ n : Type u, Fintype n
  State p := Matrix p.1 p.1 ℂ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℂ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ p X => letI := p.2; Matrix.trace X) (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev productArena : Arena where
  signature := signature.{u}
  Law R := ∀ {n : Type u} [hn : Fintype n] [DecidableEq n] (p : ℕ) (H B : Matrix n n ℂ)
    (_hH : H.IsHermitian) (_hB : B.PosSemidef)
    (_hx : (p : ℝ) * ‖(Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ)) H‖ ≤ 1 / 100000),
    (p : ℝ) ^ 2 * ‖B * (H * B - B * H)‖ ^ 2 / 25 ≤
      ((balancedWords p 4).map
        (fun w => (trace (evalWord (NormedSpace.exp H) B w)).re)).sum /
        ((balancedWords p 4).length : ℝ) -
      (R.readout () ⟨n, hn⟩ (((NormedSpace.exp H) ^ ((p : ℝ) / 4) * B) ^ 4)).re

private theorem product_rejected : ¬ productArena.{u}.Law rejected := by
  intro h
  have impossible := h (n := ULift.{u} (Fin 0)) 0 0 0
    Matrix.isHermitian_zero Matrix.PosSemidef.zero (by norm_num)
  norm_num [rejected, realize, Matrix.trace_eq_zero_of_isEmpty, balancedWords] at impossible

private theorem depends : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨⟨ULift.{u} Unit, inferInstance⟩, 0, 1, ?_⟩
  change Matrix.trace (0 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) ≠
    Matrix.trace (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ)
  norm_num [Matrix.trace_one, Fintype.card_ulift, Fintype.card_unit]

def productFamily : Registration productArena.{u} (type_of% @wordMean_sub_balanced_ge.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@wordMean_sub_balanced_ge.{u}, rejected, product_rejected⟩
  sensitivity :=
    ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, product_rejected⟩,
      fun e => nomatch e⟩
  dependence := depends

def productRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@wordMean_sub_balanced_ge.{u}) (Realization signature.{u}) Unit Unit where
  unitName :=
    `D5.S3.Quantum.Analysis.RefinedBMVNearScalarWordMean.wordMean_sub_balanced_ge.__information_unit
  realizationName := ``productFamily
  realizationSource := none
  generated := false
  arena := .source ⟨productArena.{u}⟩
  objectArena := .source ⟨productArena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source productArena.{u} ⟨productFamily.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u}
    (fun _ p X => letI := p.2; Matrix.trace X) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.WordMean
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Analysis.RefinedBMV.NearScalar.WordMean
