import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Estimation.TimeArrow.NativeProductPoisson
import Reg.Support.DependentFamily

open MeasureTheory ProbabilityTheory Finset LeanInformationAudit
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Estimation.SequentialDecisionRisk.FiniteSupportSelectionBayes
open _root_.D5.S3.Estimation.TimeArrow.ActualMarkedPathPgfPoissonEnvelope
open _root_.D5.S3.Estimation.TimeArrow.NativeMarkedCountComparison
open _root_.D5.S3.Estimation.TimeArrow.MarkedPoissonEventComparison
open _root_.D5.S3.Estimation.TimeArrow.NativeProductPoisson
open scoped NNReal Classical
noncomputable section
namespace Reg.D5.S3.Estimation.TimeArrow.NativeProductPoisson

@[reducible] def signature : Signature where
  Params := Unit
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ x => |x|) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ {M q s : ℕ} {r : ℝ}
    (hq : 1 ≤ q) (hqm : q < M) (hr : 0 < r) (hr1 : r < 1)
    (hc1 : compensation M q r < 1) (S : Support M q)
    (m : Fin q → Fin M) (hm : Function.Injective m) (hmS : ∀ j, m j ∈ S.val)
    (E : Set ((Fin q ⊕ Fin q) → ℕ)),
    R.readout () ()
      ((∑ o : Obs M s .path, if nativeCounts m o ∈ E then probability r .path S o else 0) -
        (poissonProduct (fun j : Fin q ⊕ Fin q => (s : ℝ≥0) * signalRates M r j)).real E) ≤
      9 * (s : ℝ) * (rho M q)^2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  let S : Support 2 1 := ⟨{0}, by simp⟩
  have hh := h (M := 2) (q := 1) (s := 0) (r := (1/2 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [compensation]) S (fun _ => 0)
    (fun _ _ _ => Subsingleton.elim _ _) (by intro j; simp [S]) ∅
  norm_num [rejected, realize] at hh

def family : Registration arena (type_of% (@native_product_poisson)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@native_product_poisson, rejected, rejected_law⟩
  sensitivity := ⟨fun i => ⟨rejected, fun j h => (h (Subsingleton.elim j i)).elim,
    rfl, rejected_law⟩, fun i => nomatch i⟩
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change |(0 : ℝ)| ≠ |(1 : ℝ)|
    norm_num

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@native_product_poisson)
    (type_of% (realize signature (fun _ _ x => |x|) (fun e => nomatch e)))
    Unit Unit where
  unitName := `D5.S3.Estimation.TimeArrow.NativeProductPoisson.native_product_poisson.__information_unit
  realizationName := `Reg.D5.S3.Estimation.TimeArrow.NativeProductPoisson.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ x => |x|) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Estimation.TimeArrow.NativeProductPoisson
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Estimation.TimeArrow.NativeProductPoisson
