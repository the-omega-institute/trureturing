import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity
import Reg.Support.SingleDependentReadout

/-! The original existential-window law observed through the entire literal kernel matrix. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Matrix
open scoped BigOperators ComplexOrder
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity
open LeanInformationAudit

namespace Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature
    ℕ (fun n => Fin n → ℝ) (fun n => Matrix (Fin n) (Fin n) ℂ)

def actual : Realization signature :=
  realize signature (fun _ _ x => fun i j => (K (x i - x j) : ℂ))
    (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- Retain the existential window, all cardinalities, and the complete source hypotheses. -/
def arena : Arena where
  signature := signature
  Law R := ∃ δ : ℝ, 0 < δ ∧ δ < Real.log 2 ∧
    ∀ n : ℕ, 1 ≤ n → ∀ x : Fin n → ℝ, Function.Injective x →
      (∀ i j, |x i - x j| ≤ δ) → Matrix.PosDef (R.readout () n x)

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨δ, hδ, _, h⟩
  have hp := h 1 le_rfl (fun _ => 0) (Function.injective_of_subsingleton _)
    (by intros; simpa using hδ.le)
  change Matrix.PosDef (0 : Matrix (Fin 1) (Fin 1) ℂ) at hp
  have hz := hp.diag_pos (i := (0 : Fin 1))
  simpa only [Matrix.zero_apply, lt_self_iff_false] using hz

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  obtain ⟨δ, hδ, _, h⟩ := exists_window_posDef
  let x : Fin 2 → ℝ := ![0, δ / 2]
  have hx : Function.Injective x := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [x] <;> linarith
  have hdiam : ∀ i j, |x i - x j| ≤ δ := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [x, abs_of_pos (half_pos hδ), abs_of_nonpos (by linarith : -(δ / 2) ≤ 0)] <;>
      linarith
  refine ⟨2, (fun _ => 0), x, ?_⟩
  intro he
  have hp := h 2 (by norm_num) x hx hdiam
  change (fun i j : Fin 2 => (K (0 - 0) : ℂ)) =
    (fun i j : Fin 2 => (K (x i - x j) : ℂ)) at he
  rw [← he] at hp
  have hc : (![1, -1] : Fin 2 → ℂ) ≠ 0 := by
    intro hz
    have := congrFun hz 0
    norm_num at this
  have hq := hp.dotProduct_mulVec_pos hc
  simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using hq

def evidence : Registration arena (type_of% @exists_window_posDef) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨exists_window_posDef, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

/-- Select the whole literal matrix in PosDef; the state is the original node map. -/
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@exists_window_posDef) (Realization signature) Unit Unit where
  unitName := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity.exists_window_posDef.__information_unit
  realizationName := `Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ _ x => fun i j => (K (x i - x j) : ℂ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity
    definition := none
    coordinates := #[1]
    readouts := #[{
      path := #["arg", "body", "arg", "arg", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms evidence
#print axioms registration
end Reg.D5.S3.Weil.Mertens.IntegratedExplicit.ActualKernelLocalPositivity
