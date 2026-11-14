import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Primes.ShevelevConjectureForty
import Reg.Support.DependentFamily
import Reg.Support.ShevelevCountFamilies

set_option autoImplicit false

namespace Reg.D5.S3.Arith.Primes.ShevelevConjectureForty

open _root_.D5.S3.Arith.Primes.ShevelevConjectureForty
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

noncomputable def actual : Realization signature :=
  realize signature (fun i _ n => if i then ramanujanPrime n else labosPrime n)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ H N : ℕ, ∃ n ≥ N, 1 ≤ n ∧ R.readout false () n + H < R.readout true () n

noncomputable def erased (i : Bool) : Realization signature :=
  realize signature (fun j _ n => if j = i then
    (if i then 0 else ramanujanPrime n)
    else (if j then ramanujanPrime n else labosPrime n))
    (fun e => nomatch e)

theorem erased_fails (i : Bool) : ¬arena.Law (erased i) := by
  intro h
  obtain ⟨n, _, _, hbad⟩ := h 0 0
  cases i <;> simp [erased, realize] at hbad

noncomputable def family : Registration arena (type_of% (@result)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨result, erased false, erased_fails false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased i, ?_, rfl, erased_fails i⟩
      intro j hji
      funext u n
      change Bool at i j
      change ℕ at n
      change (if j then ramanujanPrime n else labosPrime n) =
        (if j = i then (if i then 0 else ramanujanPrime n)
          else (if j then ramanujanPrime n else labosPrime n))
      have hne : j ≠ i := hji
      rw [if_neg hne]
    · intro e
      exact nomatch e
  dependence := by
    intro i
    cases i
    · refine ⟨(), (1 : ℕ), (2 : ℕ), ?_⟩
      change labosPrime 1 ≠ labosPrime 2
      intro heq
      have h1 := (Nat.sInf_mem (labosSet_nonempty 1 (by omega))).2
      have h2 := (Nat.sInf_mem (labosSet_nonempty 2 (by omega))).2
      change ramanujanCount (labosPrime 1) = 1 at h1
      change ramanujanCount (labosPrime 2) = 2 at h2
      rw [heq] at h1
      omega
    · obtain ⟨n, _, hs⟩ := exists_separation (ramanujanPrime 1)
      refine ⟨(), (1 : ℕ), n, ?_⟩
      change ramanujanPrime 1 ≠ ramanujanPrime n
      omega

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@result) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Primes.ShevelevConjectureForty.result.__information_unit
  realizationName := `Reg.D5.S3.Arith.Primes.ShevelevConjectureForty.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun i _ n => if i then ramanujanPrime n else labosPrime n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Primes.ShevelevConjectureForty
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "body", "arg", "body", "arg", "arg", "fn", "arg", "fn", "arg"]
        stateBinder := 2, functionOperand := false, stateOperand := none,
        booleanPredicate := false },
      { path := #["body", "body", "arg", "body", "arg", "arg", "arg"]
        stateBinder := 2, functionOperand := false, stateOperand := none,
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

namespace LevelCrossing

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ _ n => count n) (fun e => nomatch e)

/-- The attained value varies while the terminal-level hypothesis retains its source value. -/
def arena : Arena where
  signature := signature
  Law R := ∀ {n b : ℕ}, 1 ≤ n → n ≤ count b →
    ∃ m, 0 < m ∧ m ≤ b ∧ R.readout () () m = n

def erased : Realization signature :=
  realize signature (fun _ _ _ => 2) (fun e => nomatch e)

theorem erased_fails : ¬arena.Law erased := by
  intro h
  obtain ⟨m, _hmpos, _hmb, hm⟩ := @h 1 2 (by decide) (by decide)
  change (2 : ℕ) = 1 at hm
  omega

def family : Registration arena (type_of% (@exists_count_eq)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_count_eq, erased, erased_fails⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased, ?_, rfl, erased_fails⟩
      intro j hji
      change Unit at i j
      cases i
      cases j
      exact (hji rfl).elim
    · intro e
      exact nomatch e
  dependence := by
    intro i
    refine ⟨(), (1 : ℕ), (2 : ℕ), ?_⟩
    change count 1 ≠ count 2
    decide

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@exists_count_eq) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Primes.ShevelevConjectureForty.exists_count_eq.__information_unit
  realizationName := `Reg.D5.S3.Arith.Primes.ShevelevConjectureForty.LevelCrossing.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => count n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Primes.ShevelevConjectureForty
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg", "body", "arg", "arg", "fn", "arg"]
      stateBinder := 4
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]


end LevelCrossing

namespace AnalyticGrowth

open Filter

abbrev signature : Signature where
  Params := Unit
  State := fun _ => ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output := fun _ _ => ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

def observed (i : Bool) (n : ℕ) : ℕ :=
  if i then Nat.primeCounting n else Nat.primeCounting (2 * n)

def actual : Realization signature :=
  realize signature (fun i _ n => observed i n) (fun e => nomatch e)

def erased (i : Bool) : Realization signature :=
  realize signature (fun j _ n =>
    if j = i then (if i = false then 0 else Nat.primeCounting (2 * n))
    else observed j n) (fun e => nomatch e)

theorem erased_difference (i : Bool) (n : ℕ) :
    (erased i).readout false () n - (erased i).readout true () n = 0 := by
  cases i <;> simp [erased, realize, observed]

theorem dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 2, ?_⟩
  cases i <;> change Nat.primeCounting 0 ≠ _ <;> decide

namespace Growth

def arena : Arena where
  signature := signature
  Law R := ∀ k : ℕ, ∀ᶠ n : ℕ in atTop,
    k ≤ R.readout false () n - R.readout true () n

theorem erased_fails (i : Bool) : ¬arena.Law (erased i) := by
  intro h
  have hh := h 1
  have hf : ∀ᶠ n : ℕ in atTop, False := hh.mono fun n hn => by
    rw [erased_difference] at hn
    omega
  obtain ⟨n, hn⟩ := hf.exists
  exact hn

def family : Registration arena (type_of% (@eventually_count_ge)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨eventually_count_ge, erased false, erased_fails false⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨erased i, ?_, rfl, erased_fails i⟩
      intro j hji
      funext u n
      change Bool at i j
      change ℕ at n
      change observed (j : Bool) (n : ℕ) =
        (if (j : Bool) = (i : Bool) then
          (if (i : Bool) = false then 0 else Nat.primeCounting (2 * (n : ℕ)))
          else observed (j : Bool) (n : ℕ))
      have hne : (j : Bool) ≠ (i : Bool) := hji
      rw [if_neg hne]
    · intro e
      exact nomatch e
  dependence := dependence

noncomputable def registration :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@eventually_count_ge) (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Primes.ShevelevConjectureForty.eventually_count_ge.__information_unit
  realizationName := `Reg.D5.S3.Arith.Primes.ShevelevConjectureForty.AnalyticGrowth.Growth.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun i _ n => observed i n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Primes.ShevelevConjectureForty
    definition := none
    coordinates := #[]
    readouts := #[
      { path := #["body", "fn", "arg", "body", "arg", "fn", "arg"]
        stateBinder := 1, functionOperand := false, stateOperand := none,
        booleanPredicate := false },
      { path := #["body", "fn", "arg", "body", "arg", "arg"]
        stateBinder := 1, functionOperand := false, stateOperand := none,
        booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Growth

end AnalyticGrowth

namespace Auxiliary

noncomputable def subtrahend_le :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.subtrahend_le)
      (Realization (Reg.Support.ShevelevCountFamilies.signature (ℕ))) Unit Unit where
  unitName := `D5.S3.Arith.Primes.ShevelevConjectureForty.subtrahend_le.__information_unit
  realizationName := `Reg.Support.ShevelevCountFamilies.subtrahend_le.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨Reg.Support.ShevelevCountFamilies.subtrahend_le.targetArena⟩
  objectArena := .source ⟨Reg.Support.ShevelevCountFamilies.subtrahend_le.targetArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (Reg.Support.ShevelevCountFamilies.subtrahend_le.targetArena) ⟨Reg.Support.ShevelevCountFamilies.subtrahend_le.evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (Reg.Support.ShevelevCountFamilies.signature (ℕ))
    (fun _ _ x => Reg.Support.ShevelevCountFamilies.subtrahend_le.observed x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S3.Arith.Primes.ShevelevConjectureForty, definition := none, coordinates := #[], readouts := #[{ path := #["body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def primeCounting_succ :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.primeCounting_succ)
      (Realization (Reg.Support.ShevelevCountFamilies.signature (ℕ))) Unit Unit where
  unitName := `D5.S3.Arith.Primes.ShevelevConjectureForty.primeCounting_succ.__information_unit
  realizationName := `Reg.Support.ShevelevCountFamilies.primeCounting_succ.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨Reg.Support.ShevelevCountFamilies.primeCounting_succ.targetArena⟩
  objectArena := .source ⟨Reg.Support.ShevelevCountFamilies.primeCounting_succ.targetArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (Reg.Support.ShevelevCountFamilies.primeCounting_succ.targetArena) ⟨Reg.Support.ShevelevCountFamilies.primeCounting_succ.evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (Reg.Support.ShevelevCountFamilies.signature (ℕ))
    (fun _ _ x => Reg.Support.ShevelevCountFamilies.primeCounting_succ.observed x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S3.Arith.Primes.ShevelevConjectureForty, definition := none, coordinates := #[], readouts := #[{ path := #["body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def count_succ_le :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.count_succ_le)
      (Realization (Reg.Support.ShevelevCountFamilies.signature (ℕ))) Unit Unit where
  unitName := `D5.S3.Arith.Primes.ShevelevConjectureForty.count_succ_le.__information_unit
  realizationName := `Reg.Support.ShevelevCountFamilies.count_succ_le.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨Reg.Support.ShevelevCountFamilies.count_succ_le.targetArena⟩
  objectArena := .source ⟨Reg.Support.ShevelevCountFamilies.count_succ_le.targetArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (Reg.Support.ShevelevCountFamilies.count_succ_le.targetArena) ⟨Reg.Support.ShevelevCountFamilies.count_succ_le.evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (Reg.Support.ShevelevCountFamilies.signature (ℕ))
    (fun _ _ x => Reg.Support.ShevelevCountFamilies.count_succ_le.observed x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S3.Arith.Primes.ShevelevConjectureForty, definition := none, coordinates := #[], readouts := #[{ path := #["body", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def primeCounting_eq_of_no_prime :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.primeCounting_eq_of_no_prime)
      (Realization (Reg.Support.ShevelevCountFamilies.signature (ℕ))) Unit Unit where
  unitName := `D5.S3.Arith.Primes.ShevelevConjectureForty.primeCounting_eq_of_no_prime.__information_unit
  realizationName := `Reg.Support.ShevelevCountFamilies.primeCounting_eq_of_no_prime.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨Reg.Support.ShevelevCountFamilies.primeCounting_eq_of_no_prime.targetArena⟩
  objectArena := .source ⟨Reg.Support.ShevelevCountFamilies.primeCounting_eq_of_no_prime.targetArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (Reg.Support.ShevelevCountFamilies.primeCounting_eq_of_no_prime.targetArena) ⟨Reg.Support.ShevelevCountFamilies.primeCounting_eq_of_no_prime.evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (Reg.Support.ShevelevCountFamilies.signature (ℕ))
    (fun _ _ x => Reg.Support.ShevelevCountFamilies.primeCounting_eq_of_no_prime.observed x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S3.Arith.Primes.ShevelevConjectureForty, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "body", "body", "fn", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def count_before_double_pos :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.count_before_double_pos)
      (Realization (Reg.Support.ShevelevCountFamilies.signature (ℕ))) Unit Unit where
  unitName := `D5.S3.Arith.Primes.ShevelevConjectureForty.count_before_double_pos.__information_unit
  realizationName := `Reg.Support.ShevelevCountFamilies.count_before_double_pos.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨Reg.Support.ShevelevCountFamilies.count_before_double_pos.targetArena⟩
  objectArena := .source ⟨Reg.Support.ShevelevCountFamilies.count_before_double_pos.targetArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (Reg.Support.ShevelevCountFamilies.count_before_double_pos.targetArena) ⟨Reg.Support.ShevelevCountFamilies.count_before_double_pos.evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (Reg.Support.ShevelevCountFamilies.signature (ℕ))
    (fun _ _ x => Reg.Support.ShevelevCountFamilies.count_before_double_pos.observed x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S3.Arith.Primes.ShevelevConjectureForty, definition := none, coordinates := #[], readouts := #[{ path := #["body", "body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def count_window_left :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.count_window_left)
      (Realization (Reg.Support.ShevelevCountFamilies.signature (ℕ × ℕ))) Unit Unit where
  unitName := `D5.S3.Arith.Primes.ShevelevConjectureForty.count_window_left.__information_unit
  realizationName := `Reg.Support.ShevelevCountFamilies.count_window_left.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨Reg.Support.ShevelevCountFamilies.count_window_left.targetArena⟩
  objectArena := .source ⟨Reg.Support.ShevelevCountFamilies.count_window_left.targetArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (Reg.Support.ShevelevCountFamilies.count_window_left.targetArena) ⟨Reg.Support.ShevelevCountFamilies.count_window_left.evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (Reg.Support.ShevelevCountFamilies.signature (ℕ × ℕ))
    (fun _ _ x => Reg.Support.ShevelevCountFamilies.count_window_left.observed x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def count_window_right :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.count_window_right)
      (Realization (Reg.Support.ShevelevCountFamilies.signature (ℕ × ℕ))) Unit Unit where
  unitName := `D5.S3.Arith.Primes.ShevelevConjectureForty.count_window_right.__information_unit
  realizationName := `Reg.Support.ShevelevCountFamilies.count_window_right.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨Reg.Support.ShevelevCountFamilies.count_window_right.targetArena⟩
  objectArena := .source ⟨Reg.Support.ShevelevCountFamilies.count_window_right.targetArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (Reg.Support.ShevelevCountFamilies.count_window_right.targetArena) ⟨Reg.Support.ShevelevCountFamilies.count_window_right.evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (Reg.Support.ShevelevCountFamilies.signature (ℕ × ℕ))
    (fun _ _ x => Reg.Support.ShevelevCountFamilies.count_window_right.observed x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def primeCounting_half_floor_le :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.primeCounting_half_floor_le)
      (Realization (Reg.Support.ShevelevCountFamilies.signature (ℝ))) Unit Unit where
  unitName := `D5.S3.Arith.Primes.ShevelevConjectureForty.primeCounting_half_floor_le.__information_unit
  realizationName := `Reg.Support.ShevelevCountFamilies.primeCounting_half_floor_le.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨Reg.Support.ShevelevCountFamilies.primeCounting_half_floor_le.targetArena⟩
  objectArena := .source ⟨Reg.Support.ShevelevCountFamilies.primeCounting_half_floor_le.targetArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (Reg.Support.ShevelevCountFamilies.primeCounting_half_floor_le.targetArena) ⟨Reg.Support.ShevelevCountFamilies.primeCounting_half_floor_le.evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (Reg.Support.ShevelevCountFamilies.signature (ℝ))
    (fun _ _ x => Reg.Support.ShevelevCountFamilies.primeCounting_half_floor_le.observed x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S3.Arith.Primes.ShevelevConjectureForty, definition := none, coordinates := #[], readouts := #[{ path := #["body", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def ramanujanCount_add_half :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.ramanujanCount_add_half)
      (Realization (Reg.Support.ShevelevCountFamilies.signature (ℝ))) Unit Unit where
  unitName := `D5.S3.Arith.Primes.ShevelevConjectureForty.ramanujanCount_add_half.__information_unit
  realizationName := `Reg.Support.ShevelevCountFamilies.ramanujanCount_add_half.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨Reg.Support.ShevelevCountFamilies.ramanujanCount_add_half.targetArena⟩
  objectArena := .source ⟨Reg.Support.ShevelevCountFamilies.ramanujanCount_add_half.targetArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (Reg.Support.ShevelevCountFamilies.ramanujanCount_add_half.targetArena) ⟨Reg.Support.ShevelevCountFamilies.ramanujanCount_add_half.evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (Reg.Support.ShevelevCountFamilies.signature (ℝ))
    (fun _ _ x => Reg.Support.ShevelevCountFamilies.ramanujanCount_add_half.observed x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S3.Arith.Primes.ShevelevConjectureForty, definition := none, coordinates := #[], readouts := #[{ path := #["body", "fn", "arg", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def ramanujanCount_eq_count_floor :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.ramanujanCount_eq_count_floor)
      (Realization (Reg.Support.ShevelevCountFamilies.signature (ℝ))) Unit Unit where
  unitName := `D5.S3.Arith.Primes.ShevelevConjectureForty.ramanujanCount_eq_count_floor.__information_unit
  realizationName := `Reg.Support.ShevelevCountFamilies.ramanujanCount_eq_count_floor.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨Reg.Support.ShevelevCountFamilies.ramanujanCount_eq_count_floor.targetArena⟩
  objectArena := .source ⟨Reg.Support.ShevelevCountFamilies.ramanujanCount_eq_count_floor.targetArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (Reg.Support.ShevelevCountFamilies.ramanujanCount_eq_count_floor.targetArena) ⟨Reg.Support.ShevelevCountFamilies.ramanujanCount_eq_count_floor.evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (Reg.Support.ShevelevCountFamilies.signature (ℝ))
    (fun _ _ x => Reg.Support.ShevelevCountFamilies.ramanujanCount_eq_count_floor.observed x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S3.Arith.Primes.ShevelevConjectureForty, definition := none, coordinates := #[], readouts := #[{ path := #["body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def ramanujanCount_nat :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.ramanujanCount_nat)
      (Realization (Reg.Support.ShevelevCountFamilies.signature (ℕ))) Unit Unit where
  unitName := `D5.S3.Arith.Primes.ShevelevConjectureForty.ramanujanCount_nat.__information_unit
  realizationName := `Reg.Support.ShevelevCountFamilies.ramanujanCount_nat.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨Reg.Support.ShevelevCountFamilies.ramanujanCount_nat.targetArena⟩
  objectArena := .source ⟨Reg.Support.ShevelevCountFamilies.ramanujanCount_nat.targetArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (Reg.Support.ShevelevCountFamilies.ramanujanCount_nat.targetArena) ⟨Reg.Support.ShevelevCountFamilies.ramanujanCount_nat.evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (Reg.Support.ShevelevCountFamilies.signature (ℕ))
    (fun _ _ x => Reg.Support.ShevelevCountFamilies.ramanujanCount_nat.observed x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S3.Arith.Primes.ShevelevConjectureForty, definition := none, coordinates := #[], readouts := #[{ path := #["body", "fn", "arg"], stateBinder := 0, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def ramanujanSet_nonempty :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.ramanujanSet_nonempty)
      (Realization (Reg.Support.ShevelevCountFamilies.signature (ℝ))) Unit Unit where
  unitName := `D5.S3.Arith.Primes.ShevelevConjectureForty.ramanujanSet_nonempty.__information_unit
  realizationName := `Reg.Support.ShevelevCountFamilies.ramanujanSet_nonempty.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨Reg.Support.ShevelevCountFamilies.ramanujanSet_nonempty.targetArena⟩
  objectArena := .source ⟨Reg.Support.ShevelevCountFamilies.ramanujanSet_nonempty.targetArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (Reg.Support.ShevelevCountFamilies.ramanujanSet_nonempty.targetArena) ⟨Reg.Support.ShevelevCountFamilies.ramanujanSet_nonempty.evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (Reg.Support.ShevelevCountFamilies.signature (ℝ))
    (fun _ _ x => Reg.Support.ShevelevCountFamilies.ramanujanSet_nonempty.observed x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def labosSet_nonempty :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.labosSet_nonempty)
      (Realization (Reg.Support.ShevelevCountFamilies.signature (ℕ))) Unit Unit where
  unitName := `D5.S3.Arith.Primes.ShevelevConjectureForty.labosSet_nonempty.__information_unit
  realizationName := `Reg.Support.ShevelevCountFamilies.labosSet_nonempty.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨Reg.Support.ShevelevCountFamilies.labosSet_nonempty.targetArena⟩
  objectArena := .source ⟨Reg.Support.ShevelevCountFamilies.labosSet_nonempty.targetArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (Reg.Support.ShevelevCountFamilies.labosSet_nonempty.targetArena) ⟨Reg.Support.ShevelevCountFamilies.labosSet_nonempty.evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (Reg.Support.ShevelevCountFamilies.signature (ℕ))
    (fun _ _ x => Reg.Support.ShevelevCountFamilies.labosSet_nonempty.observed x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

noncomputable def exists_separation :
    LeanInformationAudit.Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
      (@_root_.D5.S3.Arith.Primes.ShevelevConjectureForty.exists_separation)
      (Realization (Reg.Support.ShevelevCountFamilies.signature (ℕ))) Unit Unit where
  unitName := `D5.S3.Arith.Primes.ShevelevConjectureForty.exists_separation.__information_unit
  realizationName := `Reg.Support.ShevelevCountFamilies.exists_separation.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨Reg.Support.ShevelevCountFamilies.exists_separation.targetArena⟩
  objectArena := .source ⟨Reg.Support.ShevelevCountFamilies.exists_separation.targetArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source (Reg.Support.ShevelevCountFamilies.exists_separation.targetArena) ⟨Reg.Support.ShevelevCountFamilies.exists_separation.evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize (Reg.Support.ShevelevCountFamilies.signature (ℕ))
    (fun _ _ x => Reg.Support.ShevelevCountFamilies.exists_separation.observed x) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some { owner := `D5.S3.Arith.Primes.ShevelevConjectureForty, definition := none, coordinates := #[], readouts := #[{ path := #["body", "arg", "body", "arg", "arg", "arg"], stateBinder := 1, functionOperand := false, stateOperand := none, booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Auxiliary

end Reg.D5.S3.Arith.Primes.ShevelevConjectureForty
