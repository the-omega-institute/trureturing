import D5.S3.Arith.Robin.PriceRecord.ActualRecordElementaryPrimeTails
import D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.DependentFamily

/-! Source-only audit candidate for the single all-prime endpoint.
The whole factorization function is the output; Unit is the role carrier,
not a restriction of the infinite prime domain. The Law retains the original
existential threshold, all integers, arbitrary original positive prices,
FullRecord premise and every prime in their original quantifier positions.

The existing arbitrarily_large_price_records supplies genuine original
strict records without RH. FullRecord is definitionally its objective-record
clause. No record-existence or NeBot premise is added. The complete typed
family registration below supplies the mathematical obligations in source.
The shared realize enrollment is Reg.Support.DependentFamily.enrollment_1.
Elaboration and the raw source selector/enrollment binding have NOT been
checked for this candidate; no declared_validated status is asserted.
Unfinished binding evidence remains tracked under issue #29429. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualRecordElementaryPrimeTails

open _root_.D5.S3.Arith.GoldenResource.GoldenResourceOptimalLayerCount
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualElementaryGlobalBudgetGap (ownPrice)
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualBoundaryPriceLocalization (FullRecord)
open _root_.D5.S3.Arith.Robin.OriginalEndpointPrimeTail (largestPrime)
open _root_.D5.S3.Arith.Robin.PriceRecord.FullArithmeticCorrectionSecondOrder
  (arbitrarily_large_price_records)
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

namespace eventual_actual_record_single_prime_tail

abbrev signature : Signature where
  Params := Unit
  State _ := ℕ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℕ → ℕ
  Anchor := Empty
  finiteAnchor := inferInstance

/-- The complete actual factorization family, including zero valuations. -/
def actual : Realization signature :=
  realize signature (fun _ _ m => m.factorization) (fun e => nomatch e)

/-- A whole-family intervention, exceeding the proposed bound at every prime. -/
def rejected : Realization signature :=
  realize signature
    (fun _ _ m p => optimalLayerCount (ownPrice m) p + 2) (fun e => nomatch e)

abbrev sourceScope :=
  type_of% (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordElementaryPrimeTails.eventual_actual_record_single_prime_tail)

abbrev arena : Arena where
  signature := signature
  Law V := ∃ M : ℕ, ∀ m : ℕ, M ≤ m → ∀ mu : ℝ, 0 < mu → FullRecord m mu →
    ∀ p : ℕ, p.Prime →
      V.readout () () m p ≤ optimalLayerCount (ownPrice m) p + 1

private theorem actual_law : arena.Law actual :=
  @_root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordElementaryPrimeTails.eventual_actual_record_single_prime_tail

private theorem source_bridge : sourceScope ↔ arena.Law actual := Iff.rfl

/-- Reuse the stronger existing largest-prime nonvacuity theorem. This is a
Reg helper, not a new mathematical D5 public endpoint. The bridge into
FullRecord is definitional: no change of record price or objective occurs. -/
private theorem unbounded_records (M : ℕ) :
    ∃ m : ℕ, M ≤ m ∧ ∃ mu : ℝ, 0 < mu ∧ FullRecord m mu := by
  obtain ⟨m, mu, hm2, hmu, hrecord, hP⟩ :=
    arbitrarily_large_price_records (M : ℝ)
  have hPm : largestPrime m ≤ m := by
    unfold largestPrime
    apply Finset.sup_le
    intro p hp
    exact Nat.le_of_dvd (by omega : 0 < m) (Nat.dvd_of_mem_primeFactors hp)
  have hMm : (M : ℝ) < m :=
    hP.trans_le (by exact_mod_cast hPm)
  refine ⟨m, ?_, mu, hmu, ?_⟩
  · exact_mod_cast hMm.le
  · exact hrecord

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨M, hM⟩
  obtain ⟨m, hm, mu, hmu, hrecord⟩ := unbounded_records M
  have hbad := hM m hm mu hmu hrecord 2 Nat.prime_two
  change optimalLayerCount (ownPrice m) 2 + 2 ≤
    optimalLayerCount (ownPrice m) 2 + 1 at hbad
  omega

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 1, 2, ?_⟩
  intro heq
  have htwo := congrFun heq 2
  change Nat.factorization 1 2 = Nat.factorization 2 2 at htwo
  norm_num [Nat.Prime.factorization_self Nat.prime_two] at htwo

/-- All family obligations are supplied as proof terms in the candidate.
They remain unverified until this Reg module is compiled in the owner's core. -/
def source_registration : Registration arena sourceScope where
  actual := actual
  bridge := source_bridge
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- Literal realize application uses the shared enrollment_1. The selector
is a source-derived candidate: descend through Exists' argument/lambda,
then m, M≤m, mu, 0<mu, FullRecord, p and p.Prime, and select the whole
function operand of m.factorization p on the inequality's left side.
stateBinder=1 is m (M is 0); no binder is removed into Params.
The eight body edges and the coercion-to-function occurrence must still be
confirmed against the current compiled source, not accepted from this prose. -/
def registration : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Robin.PriceRecord.ActualRecordElementaryPrimeTails.eventual_actual_record_single_prime_tail)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.ActualRecordElementaryPrimeTails.eventual_actual_record_single_prime_tail.__information_unit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.ActualRecordElementaryPrimeTails.eventual_actual_record_single_prime_tail.source_registration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨source_registration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .evidence ⟨(show True from trivial)⟩ trivial
  readout := some (realize signature (fun _ _ m => m.factorization) (fun e => nomatch e))
  variation := .evidence ⟨(show True from trivial)⟩ trivial
  sensitivity := .evidence ⟨(show True from trivial)⟩ trivial
  partialSensitivity := none
  escapeFrom := some ℕ
  sourceSelection := some {
    owner := `D5.S3.Arith.Robin.PriceRecord.ActualRecordElementaryPrimeTails
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["arg", "body", "body", "body", "body", "body", "body", "body", "body",
        "fn", "arg", "fn"]
      stateBinder := 1
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end eventual_actual_record_single_prime_tail

end Reg.D5.S3.Arith.Robin.PriceRecord.ActualRecordElementaryPrimeTails
