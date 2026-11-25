import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumProduct
import Reg.Support.DependentFamily

/-! Trace readout for the four-copy lower bound on a singular three-value spectrum. -/

namespace Reg.D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumProduct

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.RefinedBMV.FourCopyGap (wordMean)
open _root_.RefinedBMV.ThreeBlockGram.ZeroSpectrum (product_bound_scaled_zero_spectrum)
open LeanInformationAudit Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

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
  Law R := ∀ {n : Type u} [hn : Fintype n] [DecidableEq n]
    (p : ℕ) (_hp : 0 < p) {r t : ℝ} (_hr : 0 < r) (_hrt : r < t)
    (A B : Matrix n n ℂ) (hA : A.PosSemidef) (_hB : B.PosSemidef)
    (_hspectrum : ∀ a, ∃ i : Fin 3, hA.isHermitian.eigenvalues a =
      (![0,r,t] : Fin 3 → ℝ) i),
    R.readout () ⟨n, hn⟩ (((A ^ ((p : ℝ) / 4)) * B) ^ 4) ≤ wordMean p A B

private theorem product_rejected : ¬ productArena.{u}.Law rejected := by
  intro h
  have impossible := h (n := ULift.{u} (Fin 0)) 1 (by decide)
    (r := 1) (t := 2) (by norm_num) (by norm_num) 0 0
    Matrix.PosSemidef.zero Matrix.PosSemidef.zero (fun a => isEmptyElim a)
  have hr := (Complex.le_def.mp impossible).1
  norm_num [rejected, realize, wordMean, Matrix.trace_eq_zero_of_isEmpty,
    List.map_const', List.sum_replicate] at hr

private theorem depends : ObservationalDependence signature.{u} actual := by
  intro role
  refine ⟨⟨ULift.{u} Unit, inferInstance⟩, 0, 1, ?_⟩
  change Matrix.trace (0 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ) ≠
    Matrix.trace (1 : Matrix (ULift.{u} Unit) (ULift.{u} Unit) ℂ)
  norm_num [Matrix.trace_one, Fintype.card_ulift, Fintype.card_unit]

def productFamily : Registration productArena.{u}
    (type_of% @product_bound_scaled_zero_spectrum.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@product_bound_scaled_zero_spectrum.{u}, rejected, product_rejected⟩
  sensitivity :=
    ⟨fun i => ⟨rejected, fun j hj => (hj (Subsingleton.elim j i)).elim, rfl, product_rejected⟩,
      fun e => nomatch e⟩
  dependence := depends

def productRegistration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@product_bound_scaled_zero_spectrum.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `RefinedBMV.ThreeBlockGram.ZeroSpectrum.product_bound_scaled_zero_spectrum.__information_unit
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
  readout := some actual
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumProduct
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end
end Reg.D5.S3.Quantum.Analysis.RefinedBMV.SingularFourth.ZeroSpectrumProduct
