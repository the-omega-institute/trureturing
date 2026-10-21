import LeanInformationAuditInterface.Contract.Registration
import LeanInformationAuditInterface.Contract.Analysis.Source
import D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
import Reg.Support.DependentFamily
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
        · simp
        · simp
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


end Reg.D5.S3.Weil.ZetaBridge.WeilArithmeticCouplingJet
