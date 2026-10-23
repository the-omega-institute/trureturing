import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedCoefficientRealization
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedCoefficientRealization
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators Classical

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedCoefficientRealization
noncomputable section

abbrev Parameters := Σ L : ℕ,
  Σ _ : (Fin L → Bool) → PMF (Fin (L + 1)),
  Σ _ : Fin (L + 1) → ℝ,
  Σ _ : Fin L → Fin (L + 1) → ℝ, Pair L → Fin (L + 1) → ℝ

@[reducible] def signature : Signature where
  Params := Parameters
  State p := Fin p.1 → Bool
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := PMF (Fin (p.1 + 1))
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature
  (fun _ p b => p.2.1 b) (fun e => nomatch e)
def rejected : Realization signature := realize signature
  (fun _ _ _ => PMF.pure 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (L : ℕ) (p : (Fin L → Bool) → PMF (Fin (L + 1)))
    (c : Fin (L + 1) → ℝ) (ell : Fin L → Fin (L + 1) → ℝ)
    (Q : Pair L → Fin (L + 1) → ℝ)
    (_expansion : ∀ b r, (p b r).toReal = polynomial c ell Q b r),
    Realizes L (fun b r => (R.readout () ⟨L,p,c,ell,Q⟩ b r).toReal) ↔
      (∀ r, totalDemand ell Q r ≤ c r) ∧ budget ell Q ≤ 1

private theorem positive : arena.Law actual := stopped_coefficient_realization_iff
private theorem faithful_bridge : (type_of% stopped_coefficient_realization_iff) ↔
    arena.Law actual := Iff.rfl

private def xorKernel (b : Fin 2 → Bool) : PMF (Fin 3) :=
  PMF.pure (if b 0 = b 1 then 0 else 1)
private def xorConstant (r : Fin 3) : ℝ := if r = 0 then 1 else 0
private def xorLinear (_ : Fin 2) (r : Fin 3) : ℝ :=
  (if r = 1 then 1 else 0) - xorConstant r
private def xorPair (_ : Pair 2) (r : Fin 3) : ℝ :=
  2 * xorConstant r - 2 * (if r = 1 then 1 else 0)

private theorem pair_sum (g : Pair 2 → ℝ) :
    (∑ a, g a) = g ⟨(0,1),by decide⟩ := by
  have all (a : Pair 2) : a = ⟨(0,1),by decide⟩ := by
    apply Subtype.ext
    rcases a with ⟨⟨i,j⟩,h⟩
    change i.val < j.val at h
    have hi := i.isLt
    have hj := j.isLt
    apply Prod.ext
    · apply Fin.ext; dsimp; omega
    · apply Fin.ext; dsimp; omega
  apply Finset.sum_eq_single (s := Finset.univ) (f := g) (⟨(0,1),by decide⟩ : Pair 2)
  · intro a _ h; exact False.elim (h (all a))
  · simp

private theorem xor_expansion : ∀ b r,
    (xorKernel b r).toReal = polynomial xorConstant xorLinear xorPair b r := by
  intro b r
  simp only [polynomial,Fin.sum_univ_two,pair_sum]
  cases h0 : b 0 <;> cases h1 : b 1 <;> fin_cases r <;>
    norm_num [xorKernel,xorConstant,xorLinear,xorPair,h0,h1,PMF.pure_apply]

private theorem base_realizes (L : ℕ) : Realizes L
    (fun _ r => ((PMF.pure (0 : Fin (L + 1))) r).toReal) := by
  let f : Catalog true L := ⟨fun _ => 0,[],by simp,by simp,by simp,by simp⟩
  refine ⟨PMF.pure f,?_⟩
  intro b r
  simp [PMF.pure_map,f]

private theorem negative : ¬arena.Law rejected := by
  intro law
  have h := ((law 2 xorKernel xorConstant xorLinear xorPair xor_expansion).mp
    (base_realizes 2)).1 (1 : Fin 3)
  simp only [totalDemand,rowDemand,outgoing,Fin.sum_univ_two,pair_sum] at h
  norm_num [xorConstant,xorLinear,xorPair] at h

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  let p : Parameters := ⟨2,xorKernel,xorConstant,xorLinear,xorPair⟩
  refine ⟨p,fun _ => false,fun i => decide (i = 0),?_⟩
  intro h
  have hr := congrArg (fun q : PMF (Fin 3) => q 0) h
  norm_num [actual,realize,p,xorKernel,PMF.pure_apply] at hr

def evidence : Registration arena (type_of% stopped_coefficient_realization_iff) where
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
    stopped_coefficient_realization_iff
    (type_of% (realize signature actual.readout actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedCoefficientRealization.stopped_coefficient_realization_iff,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedCoefficientRealization.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨arena⟩, objectArena := .source ⟨arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source arena ⟨evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize signature (fun _ p b => p.2.1 b) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedCoefficientRealization,
    definition := none, coordinates := #[0, 1, 2, 3, 4],
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg", "body", "body", "arg", "fn", "arg"],
      stateBinder := 6, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms evidence
#print axioms registration
end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedCoefficientRealization
