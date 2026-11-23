import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Fourier.WeightedPhaseRecurrence
import Reg.Support.DependentFamily
import Batteries.Tactic.OpenPrivate

/-! The observation is the weighted loss at the time chosen in the source conclusion. -/

set_option autoImplicit false

namespace Reg.D5.S3.Fourier.WeightedPhaseRecurrence

open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Fourier.WeightedPhaseRecurrence
open LeanInformationAudit Set
open scoped BigOperators

noncomputable section

universe u

abbrev signature : Signature where
  Params := Σ J : Type u, Σ _ : Fintype J, Σ _ : J → ℝ, Σ _ : J → ℝ, J → ℝ
  State _ := ℝ
  Role := Unit
  finiteRole := inferInstance
  nonemptyRole := inferInstance
  Output _ _ := ℝ
  Anchor := Empty
  finiteAnchor := inferInstance

def actual : Realization signature.{u} :=
  realize signature (fun _ q t => @phaseLoss q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 t)
    (fun e => nomatch e)

def rejected : Realization signature.{u} :=
  realize signature (fun _ _ _ => 1) (fun e => nomatch e)

abbrev arena : Arena where
  signature := signature.{u}
  Law readout := ∀ {J : Type u} [inst : Fintype J]
    (g θ p : J → ℝ) (N : ℕ) (ε δ a R : ℝ)
    (_hN : 0 < N) (_hp : ∀ j, 0 ≤ p j) (_hpsum : ∑ j, p j = 1)
    (_hε : 1 / (N : ℝ) < ε) (_hδ : 0 < δ)
    (_hzero : ∀ k : J → ℤ, (∀ j, |k j| ≤ (N : ℤ)) →
      (∑ j, (k j : ℝ) * g j) = 0 → Real.cos (∑ j, (k j : ℝ) * θ j) = 1)
    (_hgap : ∀ k : J → ℤ, (∀ j, |k j| ≤ (N : ℤ)) →
      (∑ j, (k j : ℝ) * g j) ≠ 0 → δ ≤ |∑ j, (k j : ℝ) * g j|)
    (_hbudget : R * δ * (ε - 1 / (N : ℝ)) >
      2 * (ε * (N : ℝ) ^ Fintype.card J - (ε - 1 / (N : ℝ)))),
    ∃ t ∈ Icc a (a + R), readout.readout () ⟨J, inst, g, θ, p⟩ t < ε

private theorem rejected_law : ¬ arena.{u}.Law rejected.{u} := by
  let J := ULift.{u} Unit
  let j : J := ⟨()⟩
  have hsum (k : J → ℤ) : (∑ i, (k i : ℝ) * 1) = (k j : ℝ) := by
    rw [Fintype.sum_subsingleton _ j, mul_one]
  have hgap (k : J → ℤ) (hk : (∑ i, (k i : ℝ) * 1) ≠ 0) :
      (1 : ℝ) ≤ |∑ i, (k i : ℝ) * 1| := by
    rw [hsum] at hk ⊢
    have hi : k j ≠ 0 := fun hz => hk (by simp [hz])
    have hpos : 0 < |k j| := abs_pos.mpr hi
    exact_mod_cast (show (1 : ℤ) ≤ |k j| by omega)
  intro law
  obtain ⟨t, _, ht⟩ := law (fun _ : J => 1) (fun _ => 0) (fun _ => 1)
    2 1 1 0 8 (by norm_num) (fun _ => zero_le_one) (by simp [J])
    (by norm_num) zero_lt_one (by simp)
    (fun k _ hk => hgap k hk) (by norm_num [J])
  simp [rejected, realize] at ht

abbrev marginArena : Arena where
  signature := signature.{u}
  Law readout := ∀ {J : Type u} [inst : Fintype J]
    (g θ p : J → ℝ) (N : ℕ) (ε a R : ℝ)
    (_hN : 0 < N) (_hp : ∀ j, 0 ≤ p j) (_hpsum : ∑ j, p j = 1)
    (_hε : 1 / (N : ℝ) < ε) (_hR : 0 < R)
    (_hmargin : 0 < recurrenceMargin g θ p N ε R),
    ∃ t ∈ Icc a (a + R), readout.readout () ⟨J, inst, g, θ, p⟩ t ≤
      ε - recurrenceMargin g θ p N ε R / (R * (N : ℝ) ^ Fintype.card J)

open private frequencyBox mem_frequencyBox weights weights_nonneg triangle correction edge
  modeFrequency resonantMass sincPenalty sincBound_le_reciprocal from
  D5.S3.Fourier.WeightedPhaseRecurrence

private theorem one_dimensional_strict_budget :
    let J := ULift.{u} Unit
    (1 / 4 : ℝ) ≤ recurrenceMargin (fun _ : J => 1) (fun _ => 0) (fun _ => 1) 2 1 (11 / 2) ∧
    ¬ ((11 / 2 : ℝ) * 1 * (1 - 1 / (2 : ℝ)) >
      2 * (1 * (2 : ℝ) ^ Fintype.card J - (1 - 1 / (2 : ℝ)))) := by
  classical
  dsimp only
  let J := ULift.{u} Unit
  let j : J := ⟨()⟩
  letI : DecidableEq J := Classical.decEq J
  let s := frequencyBox (J := J) 2
  let c := weights (J := J) 2 1 (fun _ => 1)
  let ξ := modeFrequency (fun _ : J => 1)
  let φ := modeFrequency (fun _ : J => 0)
  have hξ (k : J → ℤ) : ξ k = (k j : ℝ) := by
    unfold ξ modeFrequency
    rw [Fintype.sum_subsingleton _ j, mul_one]
  have hφ (k : J → ℤ) : φ k = 0 := by simp [φ, modeFrequency]
  have hconst (k : J → ℤ) : (fun _ : J => k j) = k :=
    funext fun i => congrArg k (Subsingleton.elim j i)
  have hsum (F : ℤ → ℝ) :
      (∑ k ∈ s, F (k j)) = ∑ z ∈ Finset.Icc (-2 : ℤ) 2, F z := by
    refine Finset.sum_nbij' (fun k => k j) (fun z _ => z) ?_ ?_ ?_ ?_ ?_
    · intro k hk
      exact Finset.mem_Icc.mpr (abs_le.mp (mem_frequencyBox.mp hk j))
    · intro z hz
      exact mem_frequencyBox.mpr (fun _ => abs_le.mpr (Finset.mem_Icc.mp hz))
    · intro k _
      exact hconst k
    · simp
    · simp
  have hbox : Finset.Icc (-2 : ℤ) 2 = {-2, -1, 0, 1, 2} := by
    ext z
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  let coeff (z : ℤ) := (1 - 1 / (2 : ℝ)) * triangle 2 z + (1 / (2 : ℝ)) * correction 2 z
  have hcoef (k : J → ℤ) : c k = coeff (k j) := by
    simp only [c, coeff, weights, Fintype.prod_subsingleton _ j, Fintype.sum_subsingleton _ j,
      ite_true, Nat.cast_ofNat]
  have hA : resonantMass s c ξ φ = 1 / 2 := by
    unfold resonantMass
    rw [Finset.sum_filter]
    simp_rw [hξ, hφ, Real.cos_zero, mul_one, hcoef]
    rw [hsum (fun z => if (z : ℝ) = 0 then coeff z else 0), hbox]
    norm_num [coeff, triangle, correction, edge, Finset.sum_insert, Finset.sum_singleton]
  have hB : sincPenalty s c ξ (11 / 2) ≤ 5 / 2 := by
    unfold sincPenalty
    calc
      _ ≤ ∑ k ∈ s.filter (fun k => ξ k ≠ 0), c k * (2 / |ξ k|) := by
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_left (sincBound_le_reciprocal _ _)
          (weights_nonneg (by norm_num) (fun _ => zero_le_one) (by norm_num)
            (mem_frequencyBox.mp (Finset.mem_filter.mp hk).1))
      _ = _ := by
        rw [Finset.sum_filter]
        simp_rw [hξ, hcoef]
        rw [hsum (fun z => if (z : ℝ) ≠ 0 then coeff z * (2 / |(z : ℝ)|) else 0), hbox]
        norm_num [coeff, triangle, correction, edge, Finset.sum_insert, Finset.sum_singleton]
  constructor
  · change _ ≤ (11 / 2) * resonantMass s c ξ φ - sincPenalty s c ξ (11 / 2)
    rw [hA]
    linarith
  · norm_num [J]

private theorem rejected_margin_law : ¬ marginArena.{u}.Law rejected.{u} := by
  let J := ULift.{u} Unit
  have hmargin : 0 < recurrenceMargin (fun _ : J => 1) (fun _ => 0) (fun _ => 1) 2 1
      (11 / 2) := (by norm_num : (0 : ℝ) < 1 / 4).trans_le one_dimensional_strict_budget.{u}.1
  intro law
  obtain ⟨t, _, ht⟩ := law (fun _ : J => 1) (fun _ => 0) (fun _ => 1)
    2 1 0 (11 / 2) (by norm_num) (fun _ => zero_le_one) (by simp [J])
    (by norm_num) (by norm_num) hmargin
  have hgain : 0 < recurrenceMargin (fun _ : J => 1) (fun _ => 0) (fun _ => 1) 2 1
      (11 / 2) / ((11 / 2) * (2 : ℝ) ^ Fintype.card J) := div_pos hmargin (by positivity)
  exact (lt_irrefl (1 : ℝ)) (ht.trans_lt (sub_lt_self _ hgain))

private theorem actual_dependence : ObservationalDependence signature.{u} actual.{u} := by
  intro role
  let J := ULift.{u} Unit
  refine ⟨⟨J, inferInstance, fun _ => 1, fun _ => 0, fun _ => 1⟩, 0, Real.pi, ?_⟩
  change phaseLoss (fun _ : J => 1) (fun _ => 0) (fun _ => 1) 0 ≠
    phaseLoss (fun _ : J => 1) (fun _ => 0) (fun _ => 1) Real.pi
  norm_num [phaseLoss, J, Real.cos_pi]

def evidence : Registration arena.{u} (type_of% @weighted_phase_recurrence.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weighted_phase_recurrence.{u}, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := actual_dependence

def audit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weighted_phase_recurrence.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.WeightedPhaseRecurrence.unit
  realizationName := `Reg.D5.S3.Fourier.WeightedPhaseRecurrence.evidence
  realizationSource := none
  generated := false
  arena := .source ⟨arena⟩
  objectArena := .source ⟨arena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena ⟨evidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ q t => @phaseLoss q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.WeightedPhaseRecurrence
    definition := none
    coordinates := #[0, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body", "body", "body", "body",
        "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

def marginEvidence :
    Registration marginArena.{u} (type_of% @weighted_phase_recurrence_of_margin.{u}) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@weighted_phase_recurrence_of_margin.{u}, rejected, rejected_margin_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, ?_, rejected_margin_law⟩
      · intro j hj
        exact (hj (Subsingleton.elim _ _)).elim
      · funext e
        exact nomatch e
    · intro e
      exact nomatch e
  dependence := actual_dependence

def marginAudit : Contract.Registration.{_, _, _, 0, 0, 0, _, _, _, _, _, 0}
    (@weighted_phase_recurrence_of_margin.{u}) (Realization signature.{u}) Unit Unit where
  unitName := `Reg.D5.S3.Fourier.WeightedPhaseRecurrence.marginUnit
  realizationName := `Reg.D5.S3.Fourier.WeightedPhaseRecurrence.marginEvidence
  realizationSource := none
  generated := false
  arena := .source ⟨marginArena⟩
  objectArena := .source ⟨marginArena⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source marginArena ⟨marginEvidence⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature
    (fun _ q t => @phaseLoss q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2 t) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := some {
    owner := `D5.S3.Fourier.WeightedPhaseRecurrence
    definition := none
    coordinates := #[0, 2, 3, 4]
    readouts := #[{
      path := #["body", "body", "body", "body", "body", "body", "body", "body", "body", "body",
        "body", "body", "body", "body", "body",
        "arg", "body", "arg", "fn", "arg"]
      stateBinder := 0
      functionOperand := false
      stateOperand := some #["arg"]
      booleanPredicate := false }] }
  continuation := .unknown
  familyRecord := none
  options := #[]

end

end Reg.D5.S3.Fourier.WeightedPhaseRecurrence
