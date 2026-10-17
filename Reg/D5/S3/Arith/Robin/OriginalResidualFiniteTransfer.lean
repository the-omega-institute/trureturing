import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
import Reg.Support.DependentFamily
import Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.CenteredPairSharp
import Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.FirstMomentHigh

namespace Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer

open _root_.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
open _root_.D5.S3.Arith.Robin.ActualOddMobiusFinitePairing (mobiusPrefix)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit Finset

noncomputable section

abbrev signature : Signature where
  Params := Σ _ : ℕ, Σ _ : ℕ, ℕ → ℝ
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p F => replacement p.1 p.2.1 p.2.2 F) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N q : ℕ}, 3 ≤ N → q ≤ N - 2 →
    ∀ (a F : ℕ → ℝ) (ε c : ℝ), 0 ≤ ε → 0 ≤ c →
    (∑ m ∈ Ico N (2 * N), a m = 0) →
    (∑ m ∈ Ico N (2 * N), (m : ℝ) * a m = 0) →
    (∀ k ∈ Ico (q + 1) N, |F k - mobiusPrefix k| ≤ ε * (k : ℝ) + c) →
    |residual N a - R.readout () ⟨N, q, a⟩ F| ≤
      (ε + c / (q + 1 : ℕ)) / Real.log N * ((N : ℝ) * mass N a *
        (1 + 2 * Real.log ((N : ℝ) / (q + 1 : ℕ)) *
          (1 + Real.log (2 * (N : ℝ) / (q + 1 : ℕ))))) +
        (q + 1 : ℕ) * ((3 : ℝ) * (q : ℝ) / 2 + 2) * variation N a

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (N := 3) (q := 1) (by norm_num) (by norm_num)
    (fun _ => 0) mobiusPrefix 0 0 le_rfl le_rfl (by simp) (by simp)
    (by intro k _; simp)
  norm_num [rejected, realize,
    _root_.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.residual, mass, variation] at he

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  let a : ℕ → ℝ := fun m => if m = 3 then 1 else if m = 4 then -2
    else if m = 5 then 1 else 0
  refine ⟨⟨3, 1, a⟩, (fun _ => 0), (fun _ => 1), ?_⟩
  change replacement 3 1 a (fun _ => 0) ≠ replacement 3 1 a (fun _ => 1)
  have hb : Ico 3 6 = {3, 4, 5} := by decide
  have hh : Ico 2 3 = {2} := by decide
  have hl : 0 < Real.log ((3 : ℝ) / 2) := Real.log_pos (by norm_num)
  have hL : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  norm_num [replacement, logDifference, logPair, floorPair, hb, hh, a]

def registration : Registration arena (type_of% @originalResidual_finite_transfer) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨originalResidual_finite_transfer, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- The replacement readout observes F and retains the original theorem telescope. -/
def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@originalResidual_finite_transfer) (Realization signature) Type Unit where
  unitName := `OriginalResidualFiniteTransfer.originalResidual_finite_transfer.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p F => replacement p.1 p.2.1 p.2.2 F)
    (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
    definition := none
    coordinates := #[0, 1, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "fn", "arg", "arg", "arg"]
      stateBinder := 5
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

namespace VariationNonneg

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ N a => variation N a) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => -1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ (N : ℕ) (a : ℕ → ℝ), 0 ≤ R.readout () N a

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 1 (fun _ => 0)
  norm_num [rejected, realize] at he

def registration : Registration arena (type_of% @variation_nonneg) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨variation_nonneg, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, (fun _ => 0), (fun _ => 1), ?_⟩
    norm_num [actual, realize, variation]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@variation_nonneg) (Realization signature) Type Unit where
  unitName := `OriginalResidualFiniteTransfer.variation_nonneg.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.VariationNonneg.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ N a => variation N a) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end VariationNonneg

namespace CenteredPair

abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p a => ∑ m ∈ Ico p.1 (2*p.1), a m*centered p.2 m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N d : ℕ}, 0 < N → ∀ (a : ℕ → ℝ), 0 < d →
    |R.readout () ⟨N,d⟩ a| ≤ (d : ℝ)*variation N a

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (N := 1) (d := 1) (by norm_num) (fun _ => 0) (by norm_num)
  norm_num [rejected, realize, variation] at he

def registration : Registration arena (type_of% @centered_pair_variation_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨centered_pair_variation_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨1,2⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    have hi : Ico 1 2 = {1} := by decide
    norm_num [actual, realize, hi, centered]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@centered_pair_variation_bound) (Realization signature) Type Unit where
  unitName := `OriginalResidualFiniteTransfer.centered_pair_variation_bound.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.CenteredPair.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p a => ∑ m ∈ Ico p.1 (2*p.1), a m*centered p.2 m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 3
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end CenteredPair


namespace ReciprocalLogStep

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => Real.log (k+1 : ℕ)-Real.log (k : ℝ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k : ℕ}, 0 < k → (1 : ℝ)/(k+1 : ℕ) ≤ R.readout () () k

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (k := 1) (by norm_num)
  norm_num [rejected, realize] at he

def registration : Registration arena (type_of% @reciprocal_log_step) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨reciprocal_log_step, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    norm_num [actual, realize]
    exact ne_of_lt hl

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@reciprocal_log_step) (Realization signature) Type Unit where
  unitName := `OriginalResidualFiniteTransfer.reciprocal_log_step.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.ReciprocalLogStep.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => Real.log (k+1 : ℕ)-Real.log (k : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end ReciprocalLogStep

namespace WeightedFloor

abbrev signature : Signature where
  Params := Σ _ : ℕ, ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p m => ∑ k ∈ Ico p.2 p.1, (k : ℝ)*((m / k : ℕ)-(m / (k+1) : ℕ) : ℝ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ p _ => 2*p.1*(1+Real.log (2*(p.1 : ℝ)/p.2))+1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N h m : ℕ}, 0 < h → h < N → m < 2*N →
    R.readout () ⟨N,h⟩ m ≤ 2*N*(1+Real.log (2*(N : ℝ)/h))

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (N := 2) (h := 1) (m := 0) (by norm_num) (by norm_num) (by norm_num)
  norm_num [rejected, realize] at he <;> linarith

def registration : Registration arena (type_of% @weighted_floor_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨weighted_floor_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨2,1⟩, 0, 1, ?_⟩
    have hi : Ico 1 2 = {1} := by decide
    norm_num [actual, realize, hi]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weighted_floor_bound) (Realization signature) Type Unit where
  unitName := `OriginalResidualFiniteTransfer.weighted_floor_bound.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.WeightedFloor.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p m => ∑ k ∈ Ico p.2 p.1, (k : ℝ)*((m / k : ℕ)-(m / (k+1) : ℕ) : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
    definition := none
    coordinates := #[0, 1]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end WeightedFloor

namespace LogBounds

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Fin 2
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ N d => Real.log ((N : ℝ)/d)) (fun e => nomatch e)

def rejected (role : Fin 2) : Realization signature :=
  realize signature (fun i N d => if i = role then
    (if i = 0 then -1 else Real.log N+1) else actual.readout i N d) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N d : ℕ}, 0 < d → d ≤ N →
    0 ≤ R.readout 0 N d ∧ R.readout 1 N d ≤ Real.log N

private theorem rejected_law (role : Fin 2) : ¬ arena.Law (rejected role) := by
  intro h
  fin_cases role
  · have he := (h (N := 1) (d := 1) (by norm_num) (by norm_num)).1
    norm_num [rejected, realize] at he
  · have he := (h (N := 1) (d := 1) (by norm_num) (by norm_num)).2
    norm_num [rejected, realize] at he

def registration : Registration arena (type_of% @log_bounds) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨log_bounds, rejected 0, rejected_law 0⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected i, ?_, rfl, rejected_law i⟩
      intro j h
      funext N d
      simp only [actual, rejected, realize, if_neg h]
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨2, 1, 2, ?_⟩
    have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    simpa [actual, realize] using ne_of_gt hl

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@log_bounds) (Realization signature) Type Unit where
  unitName := `OriginalResidualFiniteTransfer.log_bounds.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.LogBounds.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ N d => Real.log ((N : ℝ)/d)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "arg", "fn", "arg"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end LogBounds

namespace WeightedLogStep

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ k => Real.log (k+1 : ℕ)-Real.log (k : ℝ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {k : ℕ}, 0 < k → (k : ℝ)*R.readout () () k ≤ 1

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (k := 1) (by norm_num)
  norm_num [rejected, realize] at he

def registration : Registration arena (type_of% @weighted_log_step) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨weighted_log_step, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    have hl : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    norm_num [actual, realize]
    exact ne_of_lt hl

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@weighted_log_step) (Realization signature) Type Unit where
  unitName := `OriginalResidualFiniteTransfer.weighted_log_step.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.WeightedLogStep.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ k => Real.log (k+1 : ℕ)-Real.log (k : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end WeightedLogStep

namespace PrefixBound

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ q => mobiusPrefix q) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ q : ℕ, |R.readout () () q| ≤ (q : ℝ)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0
  norm_num [rejected, realize] at he

def registration : Registration arena (type_of% @prefix_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prefix_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    norm_num [actual, realize, mobiusPrefix, sum_Ioc_succ_top]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prefix_bound) (Realization signature) Type Unit where
  unitName := `OriginalResidualFiniteTransfer.prefix_bound.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.PrefixBound.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ q => mobiusPrefix q) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end PrefixBound

namespace SumIndices

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ q => ∑ d ∈ Ioc 0 q, (d : ℝ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ q : ℕ, R.readout () () q = (q : ℝ)*(q+1)/2

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h 0
  norm_num [rejected, realize] at he

def registration : Registration arena (type_of% @sum_indices) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨sum_indices, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change (∑ d ∈ Ioc (0 : ℕ) 0, (d : ℝ)) ≠ ∑ d ∈ Ioc (0 : ℕ) 1, (d : ℝ)
    rw [sum_indices, sum_indices]
    norm_num

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@sum_indices) (Realization signature) Type Unit where
  unitName := `OriginalResidualFiniteTransfer.sum_indices.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.SumIndices.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ q => ∑ d ∈ Ioc 0 q, (d : ℝ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end SumIndices

namespace PrefixError

abbrev signature : Signature where
  Params := Σ _ : ℕ, Σ _ : ℕ, ℕ → ℝ
  State _ := ℕ → ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p F => ∑ k ∈ Ico p.2.1 p.1, (F k-mobiusPrefix k)*p.2.2 k) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {N h : ℕ}, 0 < h → ∀ (D F : ℕ → ℝ) {ε c : ℝ}, 0 ≤ c →
    (∀ k ∈ Ico h N, |F k-mobiusPrefix k| ≤ ε*(k : ℝ)+c) →
    |R.readout () ⟨N,h,D⟩ F| ≤ (ε+c/(h : ℝ))*(∑ k ∈ Ico h N, (k : ℝ)*|D k|)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (N := 2) (h := 1) (by norm_num) (fun _ => 0) mobiusPrefix
    (ε := 0) (c := 0) le_rfl (by intro k _; simp)
  norm_num [rejected, realize] at he

def registration : Registration arena (type_of% @prefix_error_bound) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prefix_error_bound, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨⟨2,1,(fun _ => 1)⟩, (fun _ => 0), (fun _ => 1), ?_⟩
    have hi : Ico 1 2 = {1} := by decide
    norm_num [actual, realize, hi, mobiusPrefix, sum_Ioc_succ_top]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@prefix_error_bound) (Realization signature) Type Unit where
  unitName := `OriginalResidualFiniteTransfer.prefix_error_bound.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.PrefixError.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ p F => ∑ k ∈ Ico p.2.1 p.1, (F k-mobiusPrefix k)*p.2.2 k) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
    definition := none
    coordinates := #[0, 1, 3]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end PrefixError

namespace CenteredFloor

abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ d m => (m / d : ℕ)) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {d : ℕ}, 0 < d → ∀ m : ℕ,
    R.readout () d m = (m : ℝ)/d-centered d m-((d : ℝ)-1)/(2*d)

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have he := h (d := 1) (by norm_num) 0
  norm_num [rejected, realize, centered] at he

def registration : Registration arena (type_of% @centered_floor) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨centered_floor, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨1, 0, 1, ?_⟩
    norm_num [actual, realize]

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@centered_floor) (Realization signature) Type Unit where
  unitName := `OriginalResidualFiniteTransfer.centered_floor.audit
  realizationName := `Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer.CenteredFloor.registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ d m => (m / d : ℕ)) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "fn", "arg"]
      stateBinder := 2
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }]
  }
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms registration
#print axioms audit

end CenteredFloor

end
end Reg.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer
