import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.SecondHeadBound
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.SecondHeadBound
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PreselectedResidualBound
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables
open D5.S3.Estimation.DataProcessing.MeasurablePostprocessingDefectContraction
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open MeasureTheory
open scoped BigOperators
namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.SecondHeadBound
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
  Law R := ∀ (m : ℕ) (_hm : 4 ≤ m) (a : ℕ → ℝ)
    (_pos : ∀ i, 0 ≤ a i) (_upper : ∀ i, a i ≤ 1)
    (eps : ℝ) (_heps : 0 ≤ eps) (w : PMF (Catalog false m))
    (_cap : ∀ b, measurableTotalVariation
      (w.toMeasure.map (fun f => R.readout () ⟨m,a,eps,w⟩ f b)) (finiteTarget m a b)
        ≤ ENNReal.ofReal eps),
    ((m-2)*(m+1) : ℕ)*eps ≥ (m-3 : ℕ)*a 1 +
      (m-2 : ℕ)*(∑ t ∈ Finset.Icc 2 (m-1), a t) - (m-3 : ℕ)

private theorem positive : arena.Law actual := second_head_bound
private theorem faithful_bridge : (type_of% second_head_bound) ↔ arena.Law actual := Iff.rfl

private def constant (L : ℕ) (r : Fin (L+1)) : Catalog false L :=
  ⟨fun _ => r,⟨[],by simp,by simp,by simp,by simp⟩⟩
private theorem negative : ¬ arena.Law rejected := by
  intro law
  let w : PMF (Catalog false 4) := PMF.pure (constant 4 0)
  have cap (b : Fin 4 → Bool) : measurableTotalVariation
      (w.toMeasure.map (fun f => rejected.readout () ⟨4,(fun _ => 1),0,w⟩ f b))
      (finiteTarget 4 (fun _ => 1) b) ≤ ENNReal.ofReal 0 := by
    have maplaw : w.toMeasure.map (fun f => rejected.readout () ⟨4,(fun _ => 1),0,w⟩ f b) =
        Measure.dirac (oracle 4 b) := by
      simp [w,rejected,realize,PMF.toMeasure_pure]
    have target : finiteTarget 4 (fun _ => 1) b = Measure.dirac (oracle 4 b) := by
      by_cases h : firstFalse b < 4 <;> simp [finiteTarget,oracle,h]
    rw [maplaw,target]
    simp [measurableTotalVariation]
  have bound := law 4 (by norm_num) (fun _ => 1) (by intro i; norm_num)
    (by intro i; norm_num) 0 (by norm_num) w cap
  norm_num [show Finset.Icc 2 3 = {2,3} by decide] at bound

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  let p : Parameters := ⟨4,(fun _ => 0),0,PMF.pure (constant 4 0)⟩
  refine ⟨p,constant 4 0,constant 4 1,?_⟩
  intro h
  have val := congrArg (fun f => (f (fun _ => false)).val) h
  norm_num [actual,realize,constant] at val

def evidence : Registration arena (type_of% second_head_bound) where
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
    second_head_bound (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.SecondHeadBound.second_head_bound,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.SecondHeadBound.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent, readout := some (realize signature (fun _ _ f => f.val) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.SecondHeadBound,
    definition := none, coordinates := #[0,2,5,7],
    readouts := #[{
      path := #["body","body","body","body","body","body","body","body","domain","body","fn","arg","fn","arg","fn","arg","body","fn"],
      stateBinder := 9, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms evidence
#print axioms registration
end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.SecondHeadBound
