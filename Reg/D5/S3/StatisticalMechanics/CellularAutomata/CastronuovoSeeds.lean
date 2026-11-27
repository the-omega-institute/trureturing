import LeanInformationAuditInterface.Contract.Registration
import D5.S3.StatisticalMechanics.CellularAutomata.CastronuovoSeeds
import Reg.Support.SingleDependentReadout

/-! The source Law retains every original binder and logical clause for each readout. -/

noncomputable section

namespace Reg.D5.S3.StatisticalMechanics.CellularAutomata.CastronuovoSeeds

open _root_.D5.S3.StatisticalMechanics.CellularAutomata.CastronuovoSeeds
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace XorExclusion

abbrev signature : Signature :=
  Reg.Support.SingleDependentReadout.signature (Σ _ : ℤ, ℕ)
    (fun _ => ℤ → Letter 2) (fun _ => Letter 2)

def actual : Realization signature :=
  realize signature (fun _ p P => orbit (lineStep phi) p.2 P p.1) (fun e => nomatch e)

private def rejected : Realization signature :=
  realize signature (fun _ _ _ => xorLetter) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {P : ℤ → Letter 2} (_alphabet : SeedAlphabet P) (_simple : Simple P)
    (i : ℤ) (t : ℕ), R.readout () ⟨i, t⟩ P ≠ xorLetter

private def simpleSeed (i : ℤ) : Letter 2 :=
  if i = 0 then projection 0 else if i = 1 then projection 1 else constant false

private theorem simpleSeed_alphabet : SeedAlphabet simpleSeed := by
  intro i
  unfold simpleSeed
  split
  · exact Or.inr (Or.inr ⟨0, rfl⟩)
  split
  · exact Or.inr (Or.inr ⟨1, rfl⟩)
  · exact Or.inl rfl

private theorem simpleSeed_simple : Simple simpleSeed := by
  intro j
  fin_cases j
  · refine ⟨0, rfl, fun i h => ?_⟩
    by_contra hi
    have bad := congrFun h (assignment true false)
    simp [simpleSeed, hi, projection, assignment] at bad
    split at bad <;> contradiction
  · refine ⟨1, rfl, fun i h => ?_⟩
    by_contra hi
    have bad := congrFun h (assignment false true)
    simp [simpleSeed, hi, projection, assignment] at bad
    split at bad <;> contradiction

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  exact h simpleSeed_alphabet simpleSeed_simple 0 0 rfl

private theorem dependence : ObservationalDependence signature actual := by
  intro role
  refine ⟨⟨0, 0⟩, (fun _ => constant false), (fun _ => constant true), ?_⟩
  intro h
  have bad := congrFun h (assignment false false)
  cases bad

def evidence : Registration arena (type_of% @simple_line_omits_xor) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@simple_line_omits_xor, rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := dependence

end XorExclusion

/-- A zero local rule cannot realize the negation of a projection from a seed. -/
private theorem zero_rule_incomplete {S : Type} {n k : ℕ} (hk : 0 < k)
    (move : S → ℤ → S) (P : S → Letter k) (alphabet : SeedAlphabet P) :
    ¬ Complete (liftStep (fun _ : Fin n → Bool => false) move) P := by
  let j : Fin k := ⟨0, hk⟩
  let g : Letter k := fun u => !(u j)
  intro complete
  have realized : g ∈ Realized (liftStep (fun _ : Fin n → Bool => false) move) P := by
    rw [complete]
    exact Set.mem_univ _
  obtain ⟨i, t, h⟩ := realized
  cases t with
  | zero =>
    change P i = g at h
    rcases alphabet i with hzero | hone | ⟨q, hproj⟩
    · rw [hzero] at h
      have bad := congrFun h (fun _ => false)
      cases bad
    · rw [hone] at h
      have bad := congrFun h (fun _ => true)
      cases bad
    · rw [hproj] at h
      have bad := congrFun h (fun _ => false)
      cases bad
  | succ t =>
    have bad := congrFun h (fun _ => false)
    cases bad

private theorem zero_rule_not_cyclic {n k : ℕ} (hk : 0 < k) :
    ¬ StronglyCyclicUniversal (fun _ : Fin n → Bool => false) k := by
  rintro ⟨N, P, legal, _, complete⟩
  exact zero_rule_incomplete hk ringMove P legal.2 complete

private theorem zero_rule_not_line {n k : ℕ} (hk : 0 < k) :
    ¬ Universal (fun _ : Fin n → Bool => false) k := by
  rintro ⟨P, legal, complete⟩
  exact zero_rule_incomplete hk lineMove P legal.1 complete

abbrev ruleSignature : Signature :=
  Reg.Support.SingleDependentReadout.signature ℕ (fun n => LocalRule n) (fun n => LocalRule n)

def ruleActual : Realization ruleSignature :=
  realize ruleSignature (fun _ _ rule => rule) (fun e => nomatch e)

private def rejectedRuleFamily : Realization ruleSignature :=
  realize ruleSignature (fun _ _ _ _ => false) (fun e => nomatch e)

private theorem rule_dependence : ObservationalDependence ruleSignature ruleActual := by
  intro role
  refine ⟨4, (fun _ => false), (fun _ => true), ?_⟩
  intro h
  have bad := congrFun h (fun _ => false)
  cases bad

namespace Question59

abbrev arena : Arena where
  signature := ruleSignature
  Law R := ∃ (n : ℕ) (φ : LocalRule n) (k : ℕ),
    0 < n ∧ 0 < k ∧ StronglyCyclicUniversal (R.readout () n φ) k ∧ ¬ StronglyUniversal φ k

private theorem rejected_law : ¬ arena.Law rejectedRuleFamily := by
  rintro ⟨n, φ, k, _hn, hk, positive, _⟩
  exact zero_rule_not_cyclic hk positive

def evidence : Registration arena (type_of% question_5_9) where
  actual := ruleActual
  bridge := Iff.rfl
  variation := ⟨question_5_9, rejectedRuleFamily, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law ruleActual rejectedRuleFamily rejected_law
  dependence := rule_dependence

end Question59

namespace Question56

abbrev arena : Arena where
  signature := ruleSignature
  Law R := ∃ (n : ℕ) (φ : LocalRule n) (k : ℕ),
    0 < n ∧ 0 < k ∧ Universal (R.readout () n φ) k ∧ ¬ StronglyUniversal φ k

private theorem rejected_law : ¬ arena.Law rejectedRuleFamily := by
  rintro ⟨n, φ, k, _hn, hk, positive, _⟩
  exact zero_rule_not_line hk positive

def evidence : Registration arena (type_of% question_5_6) where
  actual := ruleActual
  bridge := Iff.rfl
  variation := ⟨question_5_6, rejectedRuleFamily, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity
    arena.Law ruleActual rejectedRuleFamily rejected_law
  dependence := rule_dependence

end Question56

namespace XorExclusion

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@simple_line_omits_xor) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.CastronuovoSeeds.XorExclusion.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.CastronuovoSeeds.XorExclusion.evidence
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
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.CastronuovoSeeds
    definition := none
    coordinates := #[3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["fn", "arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end XorExclusion

namespace Question59

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@question_5_9) (Realization ruleSignature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.CastronuovoSeeds.Question59.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.CastronuovoSeeds.Question59.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize ruleSignature (fun _ _ rule => rule) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.CastronuovoSeeds
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "arg", "body", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Question59

namespace Question56

def registration :
    Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@question_5_6) (Realization ruleSignature) Unit Unit where
  unitName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.CastronuovoSeeds.Question56.unit
  realizationName := `Reg.D5.S3.StatisticalMechanics.CellularAutomata.CastronuovoSeeds.Question56.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize ruleSignature (fun _ _ rule => rule) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.StatisticalMechanics.CellularAutomata.CastronuovoSeeds
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["arg", "body", "arg", "body", "arg", "body", "arg", "arg", "fn", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Question56

end Reg.D5.S3.StatisticalMechanics.CellularAutomata.CastronuovoSeeds
