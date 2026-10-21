import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.Analysis.Source
import D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
import Reg.Support.DependentFamily
import Reg.Support.WeilArithmeticCouplingJet.Envelope
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
open LeanInformationAudit
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet

/- The two path proposals select the two complete smoothEnvelope c n
applications in the elaborated conjunction after all six original binders.
The independent Bool roles correspond to the two selected occurrences; c is
lexical ordinal 0. Both role readouts agree at actual, but each can vary alone.
Their relative state operand is the final application argument n. Paths,
coordinate lifting and enrollment E1--E8 still need the real producer/judge;
the separate Iff.rfl bridge above is not a substitute for that evidence. -/
noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@smooth_weight_envelope) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet.smooth_weight_envelope.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ c n => smoothEnvelope c n) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms familyRegistration
#print axioms registration_1
end Reg.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet

namespace Reg.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet

namespace WeightDependence

private theorem zero_mode (c : ℕ) : smoothWeight c 0 = 0 := by
  simp [smoothWeight]

/-- This proof attempt uses the actual pole and the actual convergent Gamma
series. It invokes no imported private identifier and no synthetic readout. -/
private theorem positive_mode : 0 < smoothWeight 2 1 := by
  have hL : 0 < logLength 2 := Real.log_pos (by norm_num)
  have hw : 0 < frequency 2 (1 : ℤ) := by
    unfold frequency
    norm_num only [Int.cast_one, mul_one]
    exact div_pos (mul_pos (by norm_num) Real.pi_pos) hL
  have hc : 0 < Real.cosh (logLength 2 / 2) - 1 := by
    apply sub_pos.mpr
    exact Real.one_lt_cosh.mpr (ne_of_gt (div_pos hL (by norm_num)))
  have hfactor (j : ℕ) : 0 ≤
      1 - Real.exp (-(2 * (j : ℝ) + 1 / 2) * logLength 2) := by
    apply sub_nonneg.mpr
    apply Real.exp_le_one_iff.mpr
    have hr : 0 < 2 * (j : ℝ) + 1 / 2 := by positivity
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr.le) hL.le
  have hgamma : 0 ≤ ∑' j : ℕ,
      frequency 2 (1 : ℤ) *
        (1 - Real.exp (-(2 * (j : ℝ) + 1 / 2) * logLength 2)) /
        ((2 * (j : ℝ) + 1 / 2) ^ 2 + frequency 2 (1 : ℤ) ^ 2) := by
    apply tsum_nonneg
    intro j
    exact div_nonneg (mul_nonneg hw.le (hfactor j)) (by positivity)
  have hs : Summable (fun j : ℕ =>
      frequency 2 (1 : ℤ) *
        (1 - Real.exp (-(2 * (j : ℝ) + 1 / 2) * logLength 2)) /
        ((2 * (j : ℝ) + 1 / 2) ^ 2 + frequency 2 (1 : ℤ) ^ 2)) := by
    exact (arithmetic_boundary_symbol_bound (c := 2) (by decide) (1 : ℤ)).1.of_norm
  have hp : 0 <
      2 * frequency 2 (1 : ℤ) * (Real.cosh (logLength 2 / 2) - 1) /
        (frequency 2 (1 : ℤ) ^ 2 + 1 / 4) :=
    div_pos (mul_pos (mul_pos (by norm_num) hw) hc) (by positivity)
  have hweight : smoothWeight 2 1 =
    (2 * frequency 2 (1 : ℤ) * (Real.cosh (logLength 2 / 2) - 1) /
        (frequency 2 (1 : ℤ) ^ 2 + 1 / 4) +
      ∑' j : ℕ, frequency 2 (1 : ℤ) *
        (1 - Real.exp (-(2 * (j : ℝ) + 1 / 2) * logLength 2)) /
        ((2 * (j : ℝ) + 1 / 2) ^ 2 + frequency 2 (1 : ℤ) ^ 2)) /
      (1 : ℝ) ^ 2 := by
    unfold smoothWeight
    simp only [Nat.cast_one, Int.cast_natCast, Int.cast_one, Nat.cast_zero,
      zero_add, add_zero] <;> rfl'
  rw [hweight]
  norm_num only [one_pow, div_one]
  exact add_pos_of_pos_of_nonneg hp hgamma

private theorem modes_differ : smoothWeight 2 0 ≠ smoothWeight 2 1 := by
  rw [zero_mode]
  exact ne_of_lt positive_mode

end WeightDependence

namespace Nonneg

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
  realize signature (fun _ c m => smoothWeight c m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {c m : ℕ} (hc : 2 ≤ c) (hm : 0 < m),
    0 ≤ r.readout () c m

private theorem source_reconstruction :
    (type_of% (@smooth_weight_nonneg)) ↔ arena.Law actual := Iff.rfl

private def source_type_reconstruction : LeanInformationAudit.Analysis.Reconstruction
    (type_of% (@smooth_weight_nonneg)) (arena.Law actual) := .exact

private theorem actual_law : arena.Law actual := by
  intro c m hc hm
  exact smooth_weight_nonneg hc hm

/-- A witness instance refutes the universally quantified whole Law; the Law
itself is never replaced by this instance. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have h := hall (c := 2) (m := 1) (by decide) (by decide)
  change (0 : ℝ) ≤ -1 at h
  norm_num at h

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  exact ⟨2, 0, 1, WeightDependence.modes_differ⟩

def familyRegistration : Registration arena (type_of% (@smooth_weight_nonneg)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@smooth_weight_nonneg) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet.Nonneg.smooth_weight_nonneg.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet.Nonneg.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ c m => smoothWeight c m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms familyRegistration
#print axioms registration_1
end Nonneg

namespace Antitone

/-- Bool false/true index the left/right occurrences in source order. Every
natural c and mode remains available independently of the Law's hypotheses. -/
abbrev signature : Signature where
  Params := ℕ
  State _ := ℕ
  Role := Bool
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ c m => smoothWeight c m) (fun e => nomatch e)

/-- Vary just the chosen occurrence. At n=m=1, raising the left readout or
lowering the right readout by one refutes the whole original law. -/
def intervention (i : Bool) : Realization signature := realize signature
  (fun j c m => if j = i then
    (if i then smoothWeight c m - 1 else smoothWeight c m + 1)
    else smoothWeight c m)
  (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {c n m : ℕ} (hc : 2 ≤ c) (hn : 0 < n) (hnm : n ≤ m),
    r.readout false c m ≤ r.readout true c n

private theorem source_reconstruction :
    (type_of% (@smooth_weight_antitone)) ↔ arena.Law actual := Iff.rfl

private def source_type_reconstruction : LeanInformationAudit.Analysis.Reconstruction
    (type_of% (@smooth_weight_antitone)) (arena.Law actual) := .exact

private theorem actual_law : arena.Law actual := by
  intro c n m hc hn hnm
  exact smooth_weight_antitone hc hn hnm

private theorem intervention_rejects (i : Bool) : ¬ arena.Law (intervention i) := by
  intro hall
  have h := hall (c := 2) (n := 1) (m := 1)
    (by decide) (by decide) (by decide)
  cases i with
  | false =>
      have hbad : smoothWeight 2 1 + 1 ≤ smoothWeight 2 1 := by
        simpa [intervention, realize] using h
      linarith
  | true =>
      have hbad : smoothWeight 2 1 ≤ smoothWeight 2 1 - 1 := by
        simpa [intervention, realize] using h
      linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  exact ⟨2, 0, 1, WeightDependence.modes_differ⟩

def familyRegistration : Registration arena (type_of% (@smooth_weight_antitone)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨actual_law, intervention false, intervention_rejects false⟩
  sensitivity := by
    classical
    constructor
    · intro i
      refine ⟨intervention i, ?_, rfl, intervention_rejects i⟩
      intro j hj
      funext c m
      cases i <;> cases j
      · exact (hj rfl).elim
      · simp [actual, intervention, realize] <;> rfl
      · simp [actual, intervention, realize] <;> rfl
      · exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@smooth_weight_antitone) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet.Antitone.smooth_weight_antitone.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet.Antitone.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ c m => smoothWeight c m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }, {
      path := #["body", "body", "body", "body", "body", "body", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms familyRegistration
#print axioms registration_1
end Antitone

namespace Split

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
  realize signature (fun _ c m => smoothWeight c m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ c m => smoothWeight c m + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (c : ℕ) {m : ℕ} (hm : 0 < m),
    arithmeticBoundarySymbol c (m : ℤ) = -(m : ℝ) ^ 2 * r.readout () c m -
      ∑ q ∈ Finset.range c, primeWeight q * Real.sin (frequency c (m : ℤ) * Real.log q)

private theorem source_reconstruction :
    (type_of% (@arithmetic_symbol_smooth_split)) ↔ arena.Law actual := Iff.rfl

private def source_type_reconstruction : LeanInformationAudit.Analysis.Reconstruction
    (type_of% (@arithmetic_symbol_smooth_split)) (arena.Law actual) := .exact

private theorem actual_law : arena.Law actual := by
  intro c m hm
  exact arithmetic_symbol_smooth_split c hm

/-- The unchanged original equation at c=0,m=1 and the changed equation differ
by exactly one. No c>=2 hypothesis is inserted into this theorem. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hbad := hall 0 (m := 1) (by decide)
  have hactual := arithmetic_symbol_smooth_split 0 (m := 1) (by decide)
  simp only [rejected, realize] at hbad
  norm_num only [one_pow, neg_mul, one_mul, Finset.range_zero, Finset.sum_empty,
    sub_zero] at hbad hactual
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  exact ⟨2, 0, 1, WeightDependence.modes_differ⟩

def familyRegistration : Registration arena (type_of% (@arithmetic_symbol_smooth_split)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@arithmetic_symbol_smooth_split) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet.Split.arithmetic_symbol_smooth_split.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet.Split.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ c m => smoothWeight c m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

#print axioms familyRegistration
#print axioms registration_1
end Split

/- SOURCE_ONLY_UNCOMPILED.
Splice inside the existing mirrored Reg namespace, after end Split and before
the final namespace end. Retain its current imports, opens and noncomputable
section; explicitly import Mathlib.Analysis.SpecialFunctions.Log.Basic in its
header. In particular retain Reg.Support.DependentFamily and Pi.Bounds.
This physical source owner can resolve WeightDependence's existing private
modes_differ theorem; moving this to another imported file cannot do so.
SourceSelection path, parameter/state binding and enrollment: UNVERIFIED.
-/

namespace Floor

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
  realize signature (fun _ c m => smoothWeight c m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

/-- The whole original telescope and positivity conjunct are retained.
Only the one smoothWeight occurrence in the inequality conclusion varies. -/
def arena : Arena where
  signature := signature
  Law r := ∀ {c m : ℕ} (hc : 2 ≤ c) (hm : 0 < m)
    (hw : 1 ≤ frequency c (m : ℤ)),
    0 < smoothFloor c ∧ smoothFloor c ≤ (m : ℝ) ^ 2 * r.readout () c m

private theorem source_reconstruction :
    (type_of% (@smooth_weight_floor)) ↔ arena.Law actual := Iff.rfl

private theorem actual_law : arena.Law actual := by
  intro c m hc hm hw
  exact smooth_weight_floor hc hm hw

/-- A proved threshold, rather than an additional assumption on the witness. -/
private theorem witness_frequency : 1 ≤ frequency 2 (1 : ℤ) := by
  have hlog : 0 < logLength 2 := Real.log_pos (by norm_num)
  have hlog_upper : logLength 2 ≤ 1 := by
    change Real.log (2 : ℝ) ≤ 1
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  unfold frequency
  norm_num only [Int.cast_one, mul_one]
  apply (le_div_iff₀ hlog).mpr
  linarith [Real.pi_gt_three]

/-- This instance refutes the full quantified law, which is never replaced
by a single-instance law. The frequency and floor remain the actual ones. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have hbad := (hall (c := 2) (m := 1)
    (by decide) (by decide) witness_frequency).2
  simp only [rejected, realize, Nat.cast_one] at hbad
  have hpositive := (smooth_weight_floor (c := 2) (m := 1)
    (by decide) (by decide) witness_frequency).1
  norm_num only [one_pow, one_mul] at hbad
  linarith

/-- Actual dependence compares two states of the same actual weight family;
it does not infer dependence from the rejected constant realization. -/
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  exact ⟨2, 0, 1, WeightDependence.modes_differ⟩

def familyRegistration : Registration arena (type_of% (@smooth_weight_floor)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- The single role is the complete application smoothWeight c m.
Proposed expression route: five original forall bodies, And's right argument,
the inequality's right argument, then the product's right argument. The last
application argument is the original natural state m. Parameter coordinate
0 is c, following the pinned mirror convention. These are source proposals,
NOT producer/judge evidence: path/binding/enrollment remain UNVERIFIED.
The exact reconstruction bridge above does not certify SourceSelection.
Variation, whole-family sensitivity and actual observational dependence are
carried by the enrolled dependent-family source realization, as in the pinned
registration pattern; the outer .absent fields follow that pattern.
-/
noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@smooth_weight_floor) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet.Floor.smooth_weight_floor.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet.Floor.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ c m => smoothWeight c m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "arg", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end Floor


/-! SOURCE_ONLY_UNCOMPILED r3347. The four dependent-family obligations below
are source proof candidates. They are not producer/judge enrollment evidence.
The law keeps the complete existential constant and the full positive-mode
quantifier, including c>=2; only the native smoothWeight occurrence varies. -/
namespace ActualAsymptotic

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
  realize signature (fun _ c m => smoothWeight c m) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (c : ℕ) (hc : 2 ≤ c),
    ∃ K : ℝ, 0 < K ∧ ∀ m : ℕ, 0 < m →
      |(m : ℝ) ^ 2 * r.readout () c m - Real.pi / 4| ≤ K / (m : ℝ)

private theorem source_reconstruction :
    (type_of% (@smooth_weight_actual_asymptotic)) ↔ arena.Law actual := Iff.rfl

private def source_type_reconstruction : LeanInformationAudit.Analysis.Reconstruction
    (type_of% (@smooth_weight_actual_asymptotic)) (arena.Law actual) := .exact

private theorem actual_law : arena.Law actual := by
  intro c hc
  exact smooth_weight_actual_asymptotic c hc

/-- No single K works for the constant negative readout: choose a positive
natural mode above K+1. This refutes the entire existential/forall law. -/
private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  obtain ⟨K, hK, hbound⟩ := hall 2 (by decide)
  let m : ℕ := Nat.ceil (K + 1)
  have hceil : K + 1 ≤ (m : ℝ) := Nat.le_ceil (K + 1)
  have hmR : (0 : ℝ) < m := by linarith
  have hm : 0 < m := by exact_mod_cast hmR
  have hm1 : (1 : ℝ) ≤ m := by linarith
  have hbad := hbound m hm
  change |(m : ℝ) ^ 2 * (-1) - Real.pi / 4| ≤ K / (m : ℝ) at hbad
  have hnegative : (m : ℝ) ^ 2 * (-1) - Real.pi / 4 ≤ 0 := by
    nlinarith [sq_nonneg (m : ℝ), Real.pi_pos]
  rw [abs_of_nonpos hnegative] at hbad
  have hratio : K / (m : ℝ) ≤ K := by
    simpa only [div_one] using
      (div_le_div_of_nonneg_left hK.le (by norm_num : (0 : ℝ) < 1) hm1)
  have hsmall := hbad.trans hratio
  nlinarith [sq_nonneg ((m : ℝ) - 1), Real.pi_pos]

/-- The pinned private dependence proof already distinguishes actual modes
0 and 1 at c=2, and is consumed here in its physical source owner. -/
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  exact ⟨2, 0, 1, WeightDependence.modes_differ⟩

def familyRegistration : Registration arena (type_of% (@smooth_weight_actual_asymptotic)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- Proposed source route, UNVERIFIED: two outer forall bodies; Exists's
predicate and its lambda body; And's right argument; the m and hm bodies;
then <= left, abs argument, subtraction left, multiplication right. The
selected complete smoothWeight c m application has final operand m.
The existential K and its positivity conjunct are never selected or varied.
The source-family bridge is exact, but the scoped m binder under Exists,
coordinate lifting, template lawfulness/E1--E8, and all four audit slots still
require the real producer/judge. No declared_validated is fabricated.
The current owning dependent-family enrollment is reused without modification;
its availability is not a claim that this new binding has been accepted.
Unresolved audit gap is tracked by the caller-linked issue #18940.
-/
noncomputable def registration_1 : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@smooth_weight_actual_asymptotic) (type_of% actual) Type Unit := {
  unitName := `Reg.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet.ActualAsymptotic.smooth_weight_actual_asymptotic.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet.ActualAsymptotic.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ c m => smoothWeight c m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
    definition := none
    coordinates := #[0]
    readouts := #[{
      path := #["body", "body", "arg", "body", "arg", "body", "body",
        "fn", "arg", "arg", "fn", "arg", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[] }

end ActualAsymptotic

end Reg.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet


namespace Reg.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet

namespace ExplicitSmoothKSpec

/-- c is the original parameter; m is the original natural state, without
restricting the signature to positive modes or to a single cutoff. -/
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
  realize signature (fun _ c m => smoothWeight c m) (fun e => nomatch e)

/-- A genuine replacement of the selected weight observation. Its failure at
m=1 refutes the full law; the law itself keeps every positive mode. -/
def rejected : Realization signature :=
  realize signature (fun _ c _ => Real.pi / 4 + explicitSmoothK c + 1)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ (c : ℕ) (hc : 2 ≤ c),
    0 < explicitSmoothK c ∧ ∀ m : ℕ, 0 < m →
      |(m : ℝ)^2 * r.readout () c m - Real.pi / 4| ≤
        explicitSmoothK c / (m : ℝ)

private theorem source_reconstruction :
    (type_of% (@explicitSmoothK_spec)) ↔ arena.Law actual := Iff.rfl

private def source_type_reconstruction : Analysis.Reconstruction
    (type_of% (@explicitSmoothK_spec)) (arena.Law actual) := .exact

private theorem actual_law : arena.Law actual := @explicitSmoothK_spec

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have h := (hall 2 (by decide)).2 1 (by decide)
  change |(↑(1 : ℕ) : ℝ)^2 * (Real.pi / 4 + explicitSmoothK 2 + 1) - Real.pi / 4| ≤
    explicitSmoothK 2 / (↑(1 : ℕ) : ℝ) at h
  norm_num only [Nat.cast_one, one_pow, one_mul, div_one] at h
  have hself := le_abs_self (Real.pi / 4 + explicitSmoothK 2 + 1 - Real.pi / 4)
  linarith

/-- The changed observation differs at an actual admissible source instance. -/
private theorem changed_observation :
    actual.readout () 2 1 ≠ rejected.readout () 2 1 := by
  intro heq
  have h := (explicitSmoothK_spec 2 (by decide)).2 1 (by decide)
  change smoothWeight 2 1 = Real.pi / 4 + explicitSmoothK 2 + 1 at heq
  rw [heq] at h
  norm_num only [Nat.cast_one, one_pow, one_mul, div_one] at h
  have hself := le_abs_self (Real.pi / 4 + explicitSmoothK 2 + 1 - Real.pi / 4)
  linarith

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  cases i
  exact ⟨2, 0, 1, WeightDependence.modes_differ⟩

def familyRegistration : Registration arena (type_of% (@explicitSmoothK_spec)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- Raw source selection, bound to the accepted owner bytes identified above.
The native producer must independently check this path and full reconstruction. -/
def selection : Contract.SourceSelection where
  owner := `D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
  definition := none
  coordinates := #[0]
  readouts := #[{
    path := #["body", "body", "arg", "body", "body", "fn", "arg", "arg", "fn", "arg", "arg"]
    stateBinder := 2
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

/-- An exact source model, separate from the ordinary logical equivalence. -/
def source : Analysis.Source (@explicitSmoothK_spec) :=
  Analysis.Source.ofRegistration (@explicitSmoothK_spec) familyRegistration
    source_type_reconstruction selection

/-- The outer absent fields use the source implementation's proved family slots;
unknown is used only for the residual continuation. No audit verdict is asserted. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@explicitSmoothK_spec) (type_of% (realize signature (fun _ c m => smoothWeight c m) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet.explicitSmoothK_spec.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet.ExplicitSmoothKSpec.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ c m => smoothWeight c m) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms source
#print axioms registration

end ExplicitSmoothKSpec

namespace ExplicitSmoothKLe

/-- The state is the original cutoff c. It occurs directly in the selected
complete explicitSmoothK application; no auxiliary state is introduced. -/
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
  realize signature (fun _ _ c => explicitSmoothK c) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ c => Real.sqrt (c : ℝ) * logLength c + 1)
    (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law r := ∀ {c : ℕ} (hc : 3 ≤ c),
    r.readout () () c ≤ Real.sqrt (c : ℝ) * logLength c

private theorem source_reconstruction :
    (type_of% (@explicitSmoothK_le)) ↔ arena.Law actual := Iff.rfl

private def source_type_reconstruction : Analysis.Reconstruction
    (type_of% (@explicitSmoothK_le)) (arena.Law actual) := .exact

private theorem actual_law : arena.Law actual := @explicitSmoothK_le

private theorem rejected_law : ¬ arena.Law rejected := by
  intro hall
  have h := hall (c := 3) (by decide)
  change Real.sqrt (3 : ℝ) * logLength 3 + 1 ≤
    Real.sqrt (3 : ℝ) * logLength 3 at h
  linarith

private theorem changed_observation :
    actual.readout () () 3 ≠ rejected.readout () () 3 := by
  intro heq
  have h := explicitSmoothK_le (c := 3) (by decide)
  change explicitSmoothK 3 = Real.sqrt (3 : ℝ) * logLength 3 + 1 at heq
  rw [heq] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith

/-- The native explicit constant is zero at the totalized cutoff 0 and
strictly positive at 3. The full theorem still has its original c>=3 law. -/
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 3, ?_⟩
  change explicitSmoothK 0 ≠ explicitSmoothK 3
  have hz : explicitSmoothK 0 = 0 := by simp [explicitSmoothK, logLength]
  rw [hz]
  exact ne_of_lt (explicitSmoothK_spec 3 (by decide)).1

def familyRegistration : Registration arena (type_of% (@explicitSmoothK_le)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hj
      cases i
      cases j
      exact (hj rfl).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/-- Raw source selection, bound to the accepted owner bytes identified above.
The native producer must independently check this path and full reconstruction. -/
def selection : Contract.SourceSelection where
  owner := `D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
  definition := none
  coordinates := #[]
  readouts := #[{
    path := #["body", "body", "fn", "arg"]
    stateBinder := 0
    functionOperand := false
    stateOperand := none
    booleanPredicate := false }]

/-- An exact source model, separate from the ordinary logical equivalence. -/
def source : Analysis.Source (@explicitSmoothK_le) :=
  Analysis.Source.ofRegistration (@explicitSmoothK_le) familyRegistration
    source_type_reconstruction selection

/-- The outer absent fields use the source implementation's proved family slots;
unknown is used only for the residual continuation. No audit verdict is asserted. -/
def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@explicitSmoothK_le) (type_of% (realize signature (fun _ _ c => explicitSmoothK c) (fun e => nomatch e))) Unit Unit where
  unitName := `D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet.explicitSmoothK_le.__information_unit
  realizationName := `Reg.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet.ExplicitSmoothKLe.familyRegistration
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨familyRegistration⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ c => explicitSmoothK c) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some selection
  continuation := .unknown
  familyRecord := none
  options := #[]

#print axioms familyRegistration
#print axioms source
#print axioms registration

end ExplicitSmoothKLe

end Reg.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
