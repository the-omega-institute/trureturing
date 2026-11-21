import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.SplitPrimeHostSeries
import Reg.Support.SingleDependentReadout

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Filter Set
open _root_.D5.S3.Arith.SplitPrimeHostSeries
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace Reg.D5.S3.Arith.SplitPrimeHostSeries

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ) (fun _ => ℕ → Prop)

/-- At cutoff B the readout returns precisely the eligible discriminant primes. -/
def actual : Realization signature :=
  realize signature (fun _ _ B => splittingPrime B) (fun e => nomatch e)

def emptySupport : Realization signature :=
  realize signature (fun _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law V := ∀ B : ℕ,
    (Tendsto (mass (V.readout () () B)) atTop atTop ∧ ∀ N : ℕ, ∃ d > N, splittingPrime B d) ∧
    (∀ d : ℕ, splittingPrime B d → Tendsto (mass (companionPrime d)) atTop atTop ∧
      ∀ Q : ℕ, ∃ q > Q, companionPrime d q) ∧
    ∀ q : ℕ, q.Prime → q % 8 = 3 →
      let S := fun d => splittingPrime B d ∧ companionPrime d q
      Tendsto (mass S) atTop atTop ∧ ∀ N : ℕ, ∃ d > N, S d

private theorem empty_fails : ¬ arena.Law emptySupport := by
  intro h
  have hzero (n : ℕ) : mass (fun _ => False) n = 0 := by
    apply Finset.sum_eq_zero
    intro k _
    exact Set.indicator_of_notMem (s := (fun _ : ℕ => False)) (show ¬ False from id) _
  have hx := (h 0).1.1
  change Tendsto (mass (fun _ => False)) atTop atTop at hx
  simp only [funext hzero, not_tendsto_const_atTop] at hx

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro _
  refine ⟨(), 0, 7, ?_⟩
  change splittingPrime 0 ≠ splittingPrime 7
  intro he
  have h7 : splittingPrime 0 7 := by
    refine ⟨by decide, by decide, fun p hp hpr _ => ?_⟩
    simp at hp
    subst p
    exact (Nat.not_prime_zero hpr).elim
  have h := (he ▸ h7 : splittingPrime 7 7).2.2 7 (by decide) (by decide) (by decide)
  have hz : jacobiSym (-7) 7 = 0 := jacobiSym.eq_zero_iff.2 (by decide)
  norm_num [hz] at h

def family : Registration arena (type_of% @split_prime_host_series) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@split_prime_host_series, emptySupport, empty_fails⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual emptySupport empty_fails
  dependence := actual_dependence

noncomputable def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@split_prime_host_series) (Realization signature) Unit Unit where
  unitName := .str
    `D5.S3.Arith.SplitPrimeHostSeries.split_prime_host_series
    "__information_unit"
  realizationName := .str
    `Reg.D5.S3.Arith.SplitPrimeHostSeries "family"
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
    (fun _ _ B => splittingPrime B) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.SplitPrimeHostSeries
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "fn", "arg", "fn", "arg", "fn", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Reg.D5.S3.Arith.SplitPrimeHostSeries
