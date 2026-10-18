/-
SOURCE_ONLY_UNCOMPILED. Faithful source-family Reg attempt, not binding evidence.
Merged source attempt for exactly the four new owner theorems.
The pinned envelope candidate is archived byte-for-byte in evidence; only its
demonstrated role-count and coordinate defects and their required sensitivity
proof are corrected here. No D5 or Scribe bytes are changed.
-/
import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.Analysis.Source
import D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
import Reg.Support.DependentFamily
import Mathlib.Analysis.Real.Pi.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
open LeanInformationAudit
open scoped BigOperators

noncomputable section
namespace Reg.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet

/-- c is a parameter and the selected original n is the state. All natural
fibers, including n=0 and c<2, remain in the signature. -/
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
  realize signature (fun _ c n => smoothEnvelope c n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

/-- Each selected occurrence has its own role, in source order. Actual readouts
agree; interventions change one role with the other fixed. The mass, all six
original binders and every original hypothesis stay fixed. -/
def arena : Arena where
  signature := signature
  Law r := ∀ {c n m : ℕ} (hc : 2 ≤ c) (hn : 0 < n) (hnm : n ≤ m),
    0 ≤ r.readout false c n ∧
      (m : ℝ) ^ 2 * smoothWeight c m ≤ r.readout true c n

private theorem source_reconstruction :
    (type_of% (@smooth_weight_envelope)) ↔ arena.Law actual := Iff.rfl

private def source_type_reconstruction : LeanInformationAudit.Analysis.Reconstruction
    (type_of% (@smooth_weight_envelope)) (arena.Law actual) := .exact

private theorem actual_law : arena.Law actual := by
  intro c n m hc hn hnm
  exact smooth_weight_envelope hc hn hnm

private theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := (h (c := 2) (n := 1) (m := 1)
    (by decide) (by decide) (by decide)).1
  change (0 : ℝ) ≤ -1 at hbad
  norm_num at hbad

/-- Dependence is of the actual envelope, not of the rejected constant.
The n=0 fiber is retained to expose the totalized source definition faithfully. -/
private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨2, 0, 1, ?_⟩
  change smoothEnvelope 2 0 ≠ smoothEnvelope 2 1
  let a : ℝ := 2 * Real.pi / logLength 2
  let U : ℝ := 2 * (Real.cosh (logLength 2 / 2) - 1) / a
  have hlog : 0 < logLength 2 := Real.log_pos (by norm_num)
  have ha : 0 < a := div_pos (by positivity) hlog
  have hU : 0 ≤ U := div_nonneg
    (mul_nonneg (by norm_num) (sub_nonneg.mpr (Real.one_le_cosh _))) ha.le
  have hcorrection : 0 < U + 3 / (4 * a) :=
    add_pos_of_nonneg_of_pos hU (by positivity)
  have hpi : Real.pi / 4 < 2 := by linarith [Real.pi_lt_four]
  have hexpand (n : ℕ) : smoothEnvelope 2 n =
      min (2 + U / (n : ℝ))
        (Real.pi / 4 + (U + 3 / (4 * a)) / (n : ℝ)) := rfl
  rw [hexpand 0, hexpand 1]
  simp only [Nat.cast_zero, Nat.cast_one, div_zero, div_one, add_zero]
  rw [min_eq_right hpi.le]
  exact ne_of_lt (lt_min (by linarith) (by linarith))

def familyRegistration : Registration arena (type_of% (@smooth_weight_envelope)) where
  actual := actual
  bridge := source_reconstruction
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    classical
    constructor
    · intro i
      let bad : Realization signature := realize signature
        (fun j c n => if j = i then (-1 : ℝ) else smoothEnvelope c n)
        (fun e => nomatch e)
      refine ⟨bad, ?_, rfl, ?_⟩
      · intro j hj
        funext c n
        change smoothEnvelope c n =
          (if j = i then (-1 : ℝ) else smoothEnvelope c n)
        cases i <;> cases j
        · exact (hj rfl).elim
        · rfl
        · rfl
        · exact (hj rfl).elim
      · intro hall
        have h := hall (c := 2) (n := 1) (m := 1)
          (by decide) (by decide) (by decide)
        cases i with
        | false =>
            have hbad : (0 : ℝ) ≤ -1 := by
              simpa [bad, realize] using h.1
            norm_num at hbad
        | true =>
            have hbad : (1 : ℝ) ^ 2 * smoothWeight 2 1 ≤ -1 := by
              simpa [bad, realize] using h.2
            have hmass : 0 ≤ (1 : ℝ) ^ 2 * smoothWeight 2 1 :=
              mul_nonneg (sq_nonneg _) (smooth_weight_nonneg (by decide) (by decide))
            linarith
    · intro e
      exact nomatch e
  dependence := actual_dependence

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
  escapeFrom := some ℕ
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

/-! All additional material below is SOURCE_ONLY_UNCOMPILED. The shared helper
is a Reg proof of nonconstancy of the actual owner readout, not a new owner
mathematical assertion and not an assumed positivity premise. Private owner
operands are compared with their pinned defining formulas using Lean's
standard full-transparency reflexivity tactic. -/
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
    rfl'
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
  escapeFrom := some ℕ
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
      change smoothWeight c m =
        (if j = i then
          (if i then smoothWeight c m - 1 else smoothWeight c m + 1)
          else smoothWeight c m)
      cases i <;> cases j
      · exact (hj rfl).elim
      · rfl
      · rfl
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
  escapeFrom := some ℕ
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
  escapeFrom := some ℕ
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

end Reg.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
