module

public import D5.S3.Arith.Robin.OriginalFullBandNormalizer
public import Reg.Support.DependentFamily

/-! The full original source telescope and actual-integral family evidence. -/

public section

noncomputable section
set_option autoImplicit false

open MeasureTheory Set
open _root_.D5.S3.Arith.Robin.OriginalMovingWindowMoment
open _root_.D5.S3.Arith.Robin.OriginalMovingCutRow
open _root_.D5.S3.Arith.Robin.OriginalFullBandNormalizer
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily

namespace Reg.D5.S3.Arith.Robin.OriginalFullBandNormalizer

/-- Parameters keep a, ell and R; the state is the original observation x. -/
abbrev signature : Signature where
  Params := ℝ × ℝ × ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature :=
  realize signature (fun _ p x => windowMass p.2.1 p.2.2 x) (fun e => nomatch e)

/-- Interventions vary a whole observation family; actual remains the original integral. -/
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

/-- All original binders, source limits, equality and all five conclusions are retained. -/
abbrev arena : Arena where
  signature := signature
  Law F := ∀ {a ell R x : ℝ}, 4 ≤ a → 4 ≤ ell → ell ≤ a →
    x = endpoint a → x ≤ R →
    0 < F.readout () (a, ell, R) x ∧
    x ^ (1 / 2 : ℝ) / 2 * (a / x) ^ (28 / 5 : ℝ) *
        (1 + (4 / 5 : ℝ) * x ^ (-1 / 5 : ℝ)) ≤ F.readout () (a, ell, R) x ∧
    F.readout () (a, ell, R) x ≤ x ^ (1 / 2 : ℝ) / 2 * (a / x) ^ (5 / 2 : ℝ) *
        (1 + (4 / 5 : ℝ) * a ^ (-1 / 5 : ℝ)) ∧
    x ^ (1 / 2 : ℝ) / 2 * (a / x) ^ (5 / 2 : ℝ) *
        (1 + (4 / 5 : ℝ) * a ^ (-1 / 5 : ℝ)) < x ^ (1 / 2 : ℝ) / 2 ∧
    |F.readout () (a, ell, R) x - x ^ (1 / 2 : ℝ) / 2| ≤
        (14 / 5 : ℝ) * a ^ (-1 / 5 : ℝ) * x ^ (1 / 2 : ℝ)

private lemma rejected_law : ¬ arena.Law rejected := by
  intro h
  have hbad := h (a := 4) (ell := 4) (R := endpoint 4) (x := endpoint 4)
    (by norm_num) (by norm_num) le_rfl rfl le_rfl
  exact (lt_irrefl (0 : ℝ)) hbad.1

private lemma actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(4, 4, endpoint 4), 0, endpoint 4, ?_⟩
  change windowMass 4 (endpoint 4) 0 ≠ windowMass 4 (endpoint 4) (endpoint 4)
  have hz : windowMass 4 (endpoint 4) 0 = 0 := by
    unfold windowMass
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro t ht
    have hnot : ¬ t < (0 : ℝ) := by linarith [ht.1]
    simp [kernel, hnot]
  have hp := (original_full_band_normalizer (a := 4) (ell := 4) (R := endpoint 4)
    (x := endpoint 4) (by norm_num) (by norm_num) le_rfl rfl le_rfl).1
  rw [hz]
  exact ne_of_lt hp

/-- The source law is definitionally the complete original theorem, with no normalizer hypothesis. -/
def family : Registration arena (type_of% (@original_full_band_normalizer)) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@original_full_band_normalizer, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j hji
      exact (hji (Subsingleton.elim j i)).elim
    · intro e
      exact nomatch e
  dependence := actual_dependence

/- No Contract.Registration is asserted here. The remaining obligations are the
compiled reconstruction of the original source telescope, lawful instantiation
of the enrolled realize readout, exact sourceSelection occurrence ties for the
windowMass operands and x state binder, and current producer binding evidence.
The family above supplies the exact law, whole-family intervention/sensitivity
and actual integral dependence as source proof terms; it does not by itself
establish declared_validated or source-occurrence admission. -/

end Reg.D5.S3.Arith.Robin.OriginalFullBandNormalizer
