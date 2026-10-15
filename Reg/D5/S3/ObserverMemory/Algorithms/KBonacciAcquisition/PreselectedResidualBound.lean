import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PreselectedResidualBound
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PreselectedResidualBound
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory
open scoped BigOperators
namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PreselectedResidualBound
noncomputable section

abbrev Parameters := Σ L : ℕ, Σ _ : ℕ → ℝ, Σ _ : ℝ, PMF (Catalog false L)
@[reducible] def signature : Signature where
  Params := Parameters
  State p := Catalog false p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (Fin p.1 → Bool) → Fin (p.1+1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ f => f.val) (fun e => nomatch e)
private def oracle (L : ℕ) (b : Fin L → Bool) : Fin (L+1) :=
  if h : firstFalse b < L then ⟨firstFalse b+1,by omega⟩ else 0
/-- An intervention on the readout; no adaptive table is inserted into the catalog. -/
def rejected : Realization signature :=
  realize signature (fun _ p _ => oracle p.1) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (L : ℕ) (a : ℕ → ℝ) (_upper : ∀ i, a i ≤ 1)
    (eps : ℝ) (_heps : 0 ≤ eps) (_cut : ∀ i, i < L ↔ eps < a i)
    (w : PMF (Catalog false L))
    (_cap : ∀ b, measurableTotalVariation
      (w.toMeasure.map (fun f => R.readout () ⟨L,a,eps,w⟩ f b)) (finiteTarget L a b)
        ≤ ENNReal.ofReal eps),
    residual a eps ≤ 3*eps+1-a 0

private theorem positive : arena.Law actual := preselected_residual_bound
private theorem faithful_bridge : (type_of% preselected_residual_bound) ↔ arena.Law actual := Iff.rfl

private def constant (L : ℕ) (r : Fin (L+1)) : Catalog false L :=
  ⟨fun _ => r,⟨[],by simp,by simp,by simp,by simp⟩⟩
private def spike (i : ℕ) : ℝ := if i < 3 then 1 else 0
private theorem spike_residual : residual spike 0 = 1 := by
  unfold D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PreselectedResidualBound.residual
  rw [tsum_eq_single 0]
  · norm_num [spike]
  · intro k hk
    have h : ¬ k+2 < 3 := by omega
    simp [spike,h]

private theorem negative : ¬ arena.Law rejected := by
  intro law
  let w : PMF (Catalog false 3) := PMF.pure (constant 3 0)
  have upper (i) : spike i ≤ 1 := by unfold spike; split_ifs <;> norm_num
  have cut (i) : i < 3 ↔ (0 : ℝ) < spike i := by unfold spike; split_ifs <;> simp_all
  have cap (b : Fin 3 → Bool) : measurableTotalVariation
      (w.toMeasure.map (fun f => rejected.readout () ⟨3,spike,0,w⟩ f b))
      (finiteTarget 3 spike b) ≤ ENNReal.ofReal 0 := by
    have maplaw : w.toMeasure.map (fun f => rejected.readout () ⟨3,spike,0,w⟩ f b) =
        Measure.dirac (oracle 3 b) := by
      simp [w,rejected,realize,PMF.toMeasure_pure]
    have target : finiteTarget 3 spike b = Measure.dirac (oracle 3 b) := by
      by_cases h : firstFalse b < 3 <;> simp [finiteTarget,oracle,spike,h]
    rw [maplaw,target]
    simp [measurableTotalVariation]
  have bound := law 3 spike upper 0 (by norm_num) cut w cap
  rw [spike_residual] at bound
  norm_num [spike] at bound

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  let p : Parameters := ⟨1,(fun _ => 0),0,PMF.pure (constant 1 0)⟩
  refine ⟨p,constant 1 0,constant 1 1,?_⟩
  intro h
  have val := congrArg (fun f => (f (fun _ => false)).val) h
  norm_num [actual,realize,constant] at val

def evidence : Registration arena (type_of% preselected_residual_bound) where
  actual := actual
  bridge := faithful_bridge
  variation := ⟨positive,rejected,negative⟩
  sensitivity := by
    constructor
    · intro i
      exact ⟨rejected,(by intro j hj; exact (hj (Subsingleton.elim _ _)).elim),
        (by funext e; exact nomatch e),negative⟩
    · intro e; exact nomatch e
  dependence := dependence

noncomputable def registration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    preselected_residual_bound (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PreselectedResidualBound.preselected_residual_bound,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PreselectedResidualBound.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature (fun _ _ f => f.val) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PreselectedResidualBound,
    definition := none, coordinates := #[0,1,3,6],
    readouts := #[{
      path := #["body","body","body","body","body","body","body","domain","body","fn","arg","fn","arg","fn","arg","body","fn"],
      stateBinder := 8, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms evidence
#print axioms registration
end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PreselectedResidualBound
