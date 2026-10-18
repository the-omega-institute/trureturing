/-
SOURCE_ONLY_UNCOMPILED. Faithful source-family Reg attempt, not binding evidence.
Only the changed smooth_weight_envelope is selected. No original Reg source
was supplied in the pinned input set; this candidate is not a replacement for
any caller-owned pre-existing mirror. Preserve/merge such a mirror on integration.
-/
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
import Reg.Support.DependentFamily

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
open LeanInformationAudit

noncomputable section
namespace Reg.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet

/-- c is a parameter and the selected original n is the state. All natural
fibers, including n=0 and c<2, remain in the signature. -/
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
  realize signature (fun _ c n => smoothEnvelope c n) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ _ => (-1 : ℝ)) (fun e => nomatch e)

/-- Both occurrences of the same selected envelope are varied together. The
mass, all six original binders and every original hypothesis stay fixed. -/
def arena : Arena where
  signature := signature
  Law r := ∀ {c n m : ℕ} (hc : 2 ≤ c) (hn : 0 < n) (hnm : n ≤ m),
    0 ≤ r.readout () c n ∧
      (m : ℝ) ^ 2 * smoothWeight c m ≤ r.readout () c n

private theorem source_reconstruction :
    (type_of% (@smooth_weight_envelope)) ↔ arena.Law actual := Iff.rfl

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
  cases i
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

/- The two path proposals select the two complete smoothEnvelope c n
applications in the elaborated conjunction after all six original binders.
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
    coordinates := #[1]
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
