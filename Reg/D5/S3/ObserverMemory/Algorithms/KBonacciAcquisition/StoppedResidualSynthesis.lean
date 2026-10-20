import Batteries.Tactic.OpenPrivate
import D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedResidualSynthesis
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration

open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedResidualSynthesis
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PreselectedResidualBound
open D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.OriginalScheduledWitnessTables
open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open scoped BigOperators

namespace Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedResidualSynthesis
noncomputable section

private def constant (L : ℕ) (r : Fin (L+1)) : Catalog true L :=
  ⟨fun _ => r,[],by simp,by simp,by simp,by simp⟩

namespace Subset
abbrev Parameters := Σ _ : ℕ, ℕ
@[reducible] def signature : Signature where
  Params := Parameters
  State p := Catalog true p.1
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := (Fin p.1 → Bool) → Fin (p.1+1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ f => f.val) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ _ _ _ => 0) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (L m : ℕ) (hmL : m ≤ L) (hm : 3 ≤ m),
    let w := subsetLaw L m hmL hm
    ∀ b : Fin L → Bool,
      (∀ n (hn : n < m), lowReply b n = false →
        (∀ i < n, lowReply b i = true) →
        (w.map (fun f => R.readout () ⟨L,m⟩ f b) ⟨n+1,by dsimp; omega⟩).toReal = 3/(m+1:ℝ)) ∧
      (w.map (fun f => R.readout () ⟨L,m⟩ f b) 0).toReal =
        (Nat.choose (positives m b).card 2 : ℝ)/(Nat.choose (m+1) 3 : ℝ) ∧
      (∀ r : Fin (L+1), m < r.val → w.map (fun f => R.readout () ⟨L,m⟩ f b) r = 0) ∧
      ((∀ i < m, lowReply b i = true) →
        (w.map (fun f => R.readout () ⟨L,m⟩ f b) 0).toReal = 3/(m+1:ℝ))

private theorem positive : arena.Law actual := stopped_subset_law
private theorem faithful_bridge : (type_of% stopped_subset_law) ↔ arena.Law actual := Iff.rfl
private theorem negative : ¬arena.Law rejected := by
  intro law
  have h := (law 3 3 le_rfl (by decide) (fun _ => false)).1 0 (by decide)
    (by simp [lowReply]) (by intro i hi; omega)
  norm_num [rejected,realize,PMF.map_const,PMF.pure_apply] at h
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨1,1⟩,constant 1 0,constant 1 1,?_⟩
  intro h
  have v := congrArg (fun f => (f (fun _ => false)).val) h
  norm_num [actual,realize,constant] at v

def evidence : Registration arena (type_of% stopped_subset_law) where
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
end Subset

namespace Residual
abbrev Parameters := Σ _ : ℕ, Σ _ : (ℕ → ℝ), ℝ
@[reducible] def signature : Signature where
  Params := Parameters
  State p := PMF (Catalog true p.1)
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ p := PMF (Catalog true p.1)
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature := realize signature (fun _ _ w => w) (fun e => nomatch e)
def rejected : Realization signature := realize signature (fun _ p _ => PMF.pure (constant p.1 0)) (fun e => nomatch e)

@[reducible] def arena : Arena where
  signature := signature
  Law R := ∀ (L : ℕ) (_hL : 3 ≤ L) (a : ℕ → ℝ) (_ha : Antitone a)
    (_bound : a 0 ≤ 1) (eps : ℝ) (_heps : 0 < eps)
    (_cut : ∀ i, i < L ↔ eps < a i) (_cap : residual a eps ≤ 3*eps),
    ∃ w : PMF (Catalog true L),
      (∀ b : Fin L → Bool, ∀ hn : firstFalse b < L,
        ((R.readout () ⟨L,a,eps⟩ w).map (fun f => f.val b) ⟨firstFalse b+1,by dsimp; omega⟩).toReal = a (firstFalse b)-eps ∧
        1-residual a eps/3 ≤ ((R.readout () ⟨L,a,eps⟩ w).map (fun f => f.val b) 0).toReal +
          ((R.readout () ⟨L,a,eps⟩ w).map (fun f => f.val b) ⟨firstFalse b+1,by dsimp; omega⟩).toReal) ∧
      ((R.readout () ⟨L,a,eps⟩ w).map (fun f => f.val (fun _ => true)) 0).toReal = 1-residual a eps/3

private theorem positive : arena.Law actual := stopped_residual_synthesis
private theorem faithful_bridge : (type_of% stopped_residual_synthesis) ↔ arena.Law actual := Iff.rfl
private def spike (i : ℕ) : ℝ := if i < 3 then 1 else 0
open private residual_finite from
  D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.PreselectedResidualBound
private theorem negative : ¬arena.Law rejected := by
  intro law
  have mono : Antitone spike := by
    intro i j hij
    unfold spike
    split_ifs <;> norm_num <;> omega
  have cut (i) : i < 3 ↔ (1/4:ℝ) < spike i := by
    unfold spike; split_ifs <;> norm_num <;> omega
  have cap : residual spike (1/4) ≤ 3*(1/4) := by
    rw [residual_finite 3 spike (1/4) cut]
    norm_num [spike]
  obtain ⟨w,rows,_⟩ := law 3 (by decide) spike mono (by norm_num [spike]) (1/4) (by norm_num) cut cap
  have first : firstFalse (fun _ : Fin 3 => false) = 0 := by
    unfold firstFalse
    apply (Nat.find_eq_iff _).mpr
    simp [lowReply]
  have h := (rows (fun _ => false) (by rw [first]; decide)).1
  norm_num [rejected,realize,PMF.pure_map,first,spike,constant,PMF.pure_apply] at h
private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨1,(fun _ => 0),0⟩,PMF.pure (constant 1 0),PMF.pure (constant 1 1),?_⟩
  intro h
  have v := congrArg (fun p : PMF (Catalog true 1) => p (constant 1 0)) h
  have ne : constant 1 0 ≠ constant 1 1 := by
    intro h
    have v := congrArg (fun f : Catalog true 1 => (f.val (fun _ => false)).val) h
    norm_num [constant] at v
  norm_num [actual,realize,PMF.pure_apply,ne] at v

def evidence : Registration arena (type_of% stopped_residual_synthesis) where
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
end Residual

noncomputable def subsetRegistration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    stopped_subset_law (type_of% (realize Subset.signature Subset.actual.readout Subset.actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedResidualSynthesis.stopped_subset_law,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedResidualSynthesis.Subset.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨Subset.arena⟩, objectArena := .source ⟨Subset.arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source Subset.arena ⟨Subset.evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Subset.signature (fun _ _ f => f.val) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedResidualSynthesis,
    definition := none, coordinates := #[0,1],
    readouts := #[
      { path := #["body","body","body","body","body","body","fn","arg","body","body","body","body","fn","arg","arg","fn","arg","fn","arg","body","fn"], stateBinder := 10, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

noncomputable def residualRegistration : LeanInformationAudit.Contract.Registration.{0,0,1,0,0,0,0,0,0,0,0,0}
    stopped_residual_synthesis (type_of% (realize Residual.signature Residual.actual.readout Residual.actual.anchor)) Unit Unit := {
  unitName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedResidualSynthesis.stopped_residual_synthesis,
  realizationName := `Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedResidualSynthesis.Residual.evidence,
  realizationSource := none, generated := false,
  arena := .source ⟨Residual.arena⟩, objectArena := .source ⟨Residual.arena⟩,
  catalog := Lean.Name.anonymous, localNames := false,
  realization := .source Residual.arena ⟨Residual.evidence⟩,
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .absent,
  readout := some (realize Residual.signature (fun _ _ w => w) (fun e => nomatch e)),
  variation := .absent, sensitivity := .absent, partialSensitivity := none, escapeFrom := none,
  sourceSelection := some {
    owner := `D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedResidualSynthesis,
    definition := none, coordinates := #[0,2,5],
    readouts := #[
      { path := #["body","body","body","body","body","body","body","body","body","arg","body","fn","arg","body","body","fn","arg","fn","arg","arg","fn","arg","arg"], stateBinder := 9, functionOperand := false, stateOperand := none, booleanPredicate := false }] },
  continuation := .unknown, familyRecord := none, options := #[] }

#print axioms subsetRegistration
#print axioms residualRegistration

#print axioms Subset.evidence
#print axioms Residual.evidence
end
end Reg.D5.S3.ObserverMemory.Algorithms.KBonacciAcquisition.StoppedResidualSynthesis
