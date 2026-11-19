import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Arith.Abundancy.StrongPseudoperfectDensity
import Reg.Support.SingleDependentReadout

/-! A source family for the limit of the strongly pseudoperfect counting ratio. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Filter Real LeanInformationAudit
open scoped Topology
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Arith.Abundancy.StrongPseudoperfectDensity

namespace Reg.D5.S3.Arith.Abundancy.StrongPseudoperfectDensity

namespace Limit

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℕ → ℝ)
    (fun _ => Filter ℕ → Filter ℝ → Prop)

def actual : Realization signature :=
  realize signature (fun _ _ f => Tendsto f) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ _ _ => False) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := R.readout () () (fun n => (spCount n : ℝ) / n) atTop (𝓝 0)

private theorem rejected_law : ¬ arena.Law rejected := by
  exact id

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Abundancy.StrongPseudoperfectDensity.result) where
  actual := actual
  bridge := Iff.rfl
  variation :=
    ⟨@_root_.D5.S3.Arith.Abundancy.StrongPseudoperfectDensity.result,
      rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), (fun _ : ℕ => 0), (fun _ : ℕ => 1), ?_⟩
    intro he
    have he' := congrFun (congrFun he atTop) (𝓝 (0 : ℝ))
    have hh : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 0) :=
      Eq.mp he' tendsto_const_nhds
    have hzero : (1 : ℝ) = 0 :=
      tendsto_nhds_unique tendsto_const_nhds hh
    norm_num at hzero

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Abundancy.StrongPseudoperfectDensity.result)
    (Realization signature) Type Unit where
  unitName := `D5.S3.Arith.Abundancy.StrongPseudoperfectDensity.result.audit
  realizationName :=
    `Reg.D5.S3.Arith.Abundancy.StrongPseudoperfectDensity.Limit.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Abundancy.StrongPseudoperfectDensity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["fn", "fn", "fn"]
      stateBinder := 0
      functionOperand := true
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end Limit

namespace PrimeCodes

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit
    (fun _ => ℕ) (fun _ => Finset ℕ)

def actual : Realization signature :=
  realize signature (fun _ _ m => primeCodes m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => ∅) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature
  Law R := ∀ {m q : ℕ}, q.Prime → ¬ q ∣ m →
    StronglyPseudoperfect (m * q) → q ∈ R.readout () () m

private theorem six_stronglyPseudoperfect : StronglyPseudoperfect 6 := by
  refine ⟨by norm_num, (6 : ℕ).divisors, Finset.Subset.rfl, ?_, ?_⟩
  · intro d hd
    constructor
    · intro h
      apply Nat.mem_divisors.mpr
      exact ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), by norm_num⟩
    · intro h
      exact hd
  · rw [show (6 : ℕ).divisors = {1, 2, 3, 6} by decide]
    norm_num

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have h' := h (m := 3) (q := 2) (by norm_num) (by norm_num)
    six_stronglyPseudoperfect
  simpa [rejected, realize] using h'

def family : Registration arena
    (type_of% @_root_.D5.S3.Arith.Abundancy.StrongPseudoperfectDensity.prime_mem_codes) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨prime_mem_codes, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    change primeCodes 0 ≠ primeCodes 1
    norm_num [primeCodes, Finset.ext_iff,
      show ({1} : Finset ℕ).powerset = {∅, {1}} by decide]

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@_root_.D5.S3.Arith.Abundancy.StrongPseudoperfectDensity.prime_mem_codes)
    (Realization signature) Unit Unit where
  unitName := `D5.S3.Arith.Abundancy.StrongPseudoperfectDensity.prime_mem_codes.audit
  realizationName := `Reg.D5.S3.Arith.Abundancy.StrongPseudoperfectDensity.PrimeCodes.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature actual.readout actual.anchor)
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Arith.Abundancy.StrongPseudoperfectDensity
    definition := none
    coordinates := #[]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := none
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end PrimeCodes

end Reg.D5.S3.Arith.Abundancy.StrongPseudoperfectDensity
