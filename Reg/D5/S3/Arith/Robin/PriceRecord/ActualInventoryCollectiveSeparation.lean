import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Robin.PriceRecord.ActualInventoryCollectiveSeparation
import Reg.Support.DependentFamily

/-! Faithful source/readout attempt for the exact closed witness. The typed
bridge, variation, whole-role sensitivity and observational dependence are
separate from producer source-selection and enrollment validation. -/
noncomputable section
set_option autoImplicit false
namespace Reg.D5.S3.Arith.Robin.PriceRecord.ActualInventoryCollectiveSeparation
open _root_.D5.S3.Arith.Robin.PriceRecord.ActualInventoryCollectiveSeparation
open _root_.D5.S3.Arith.GoldenResourceOptimalInteger
open _root_.D5.S3.Weil.GronwallLowerEnvelope
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit

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
  realize signature (fun _ _ n => robinLogMargin n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (0 : ℝ)) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∃ z α β : ℝ, OwnClockInventorySingletons witnessN z α β ∧
      34 < z ∧ z < 35 ∧ ⌊z⌋₊ = 34 ∧ 31 < α ∧ β < 37 ∧
      witnessN = 2 ^ 6 * 3 ^ 3 * 5 ^ 2 * 7 ^ 2 * 11 * 13 * 17 * 19 * 23 * 29 * 31 ∧
      (37 * 41 * 43 * 47 : ℕ) = 3065857 ∧
      witnessM = witnessN * (37 * 41 * 43 * 47) ∧
      (1 + 1 / (37 : ℝ)) * (1 + 1 / 41) * (1 + 1 / 43) * (1 + 1 / 47) =
        3370752 / 3065857 ∧
      (∀ p ∈ ({37, 41, 43, 47} : Finset ℕ), p.Prime ∧ ¬p ∣ witnessN) ∧
      0 < R.readout () () witnessM ∧
      R.readout () () witnessM < R.readout () () witnessN

private theorem rejected_law : ¬ arena.Law rejected := by
  rintro ⟨z, α, β, _, _, _, _, _, _, _, _, _, _, _, hpos, _⟩
  change (0 : ℝ) < 0 at hpos
  exact (lt_irrefl 0) hpos

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  obtain ⟨z, α, β, _, _, _, _, _, _, _, _, _, _, _, _, hlt⟩ := actual_witness
  refine ⟨(), witnessM, witnessN, ?_⟩
  exact hlt.ne

def family : Registration arena (type_of% (@actual_witness)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨actual_witness, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@actual_witness)
    (type_of% (realize signature (fun _ _ n => robinLogMargin n) (fun e => nomatch e)))
    Type Unit where
  unitName := `D5.S3.Arith.Robin.PriceRecord.ActualInventoryCollectiveSeparation.actual_witness.audit
  realizationName := `Reg.D5.S3.Arith.Robin.PriceRecord.ActualInventoryCollectiveSeparation.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ n => robinLogMargin n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := some ℕ
  -- The source has closed integer constants rather than an original Nat binder.
  -- No invented state binder or guessed source coordinate is submitted.
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms family
#print axioms audit
end Reg.D5.S3.Arith.Robin.PriceRecord.ActualInventoryCollectiveSeparation
