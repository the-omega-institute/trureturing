import LeanInformationAudit.Syntax
import D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure
import D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration
import Reg.Support.PointwiseEqualityRegistrations
import Reg.Support.MechanicalDyadicRegistration

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.distributionArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_apply_Iic,
      statementIdentity := "sha256:e86fbc9eb0eaf8616805c1ac35ac784e9bc227197d2020c6eb701448fc79cf84",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.hitArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_singleton_hit,
      statementIdentity := "sha256:d87425086d24ff5a43a67d2dfda1cbd186660c10682806030831e672a496b283",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.supportArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_support,
      statementIdentity := "sha256:578195477c952f318d98ac2002403e3f637cf1444a98e508a938820465abb21a",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.leftJumpArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_readout_left_jump_exact,
      statementIdentity := "sha256:f63d30a471314f53d52edd81663e251c8fa9d83f96353d7d8a1eb3cad0373045",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.rationalJumpArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_rational_left_jump_closed_form,
      statementIdentity := "sha256:f0bf059491cefbf0ae23bfd82a712d76dc87b380a5f51575eff9fc07955fad01",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure }]
  source := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.distributionArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_apply_Iic,
      statementIdentity := "sha256:e86fbc9eb0eaf8616805c1ac35ac784e9bc227197d2020c6eb701448fc79cf84",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.hitArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_singleton_hit,
      statementIdentity := "sha256:d87425086d24ff5a43a67d2dfda1cbd186660c10682806030831e672a496b283",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.supportArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_support,
      statementIdentity := "sha256:578195477c952f318d98ac2002403e3f637cf1444a98e508a938820465abb21a",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.leftJumpArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_readout_left_jump_exact,
      statementIdentity := "sha256:f63d30a471314f53d52edd81663e251c8fa9d83f96353d7d8a1eb3cad0373045",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure },
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.rationalJumpArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_rational_left_jump_closed_form,
      statementIdentity := "sha256:f0bf059491cefbf0ae23bfd82a712d76dc87b380a5f51575eff9fc07955fad01",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure }]
  companionPrefix := some `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure }

noncomputable section
namespace Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure

open Set MeasureTheory
open LeanInformationAudit
open _root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure
open D5.S3.ConceptDynamics.InformationEscape
open D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration
open D5.S3.ConceptDynamics.InformationEscape.PointwiseRegistrationTemplates
open D5.S3.ConceptDynamics.InformationEscape.MechanicalDyadicRegistration
open scoped Topology

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

attribute [local instance] Classical.propDecidable

local instance : DecidableEq DistributionOutput := Classical.decEq _
local instance : DecidableEq HitOutput := Classical.decEq _
local instance : DecidableEq SupportOutput := Classical.decEq _
local instance : DecidableEq JumpOutput := Classical.decEq _
local instance : DecidableEq distributionArena.State := distributionArena.toArena.stateDecidableEq
local instance : DecidableEq hitArena.State := hitArena.toArena.stateDecidableEq
local instance : DecidableEq supportArena.State := supportArena.toArena.stateDecidableEq

private def distributionSample : DistributionInput where
  ratio := 0
  threshold := 0
  phase := 0

private def hitSample : HitInput where
  ratio := 0
  phase := 0
  threshold := 1 / 2

private def supportSample : SupportInput where
  ratio := 1 / 2
  phase := 0

theorem distributionBridge : LegacyPrimitiveRealization distributionArena.toPrimitiveLawArena
    (∀ (r alpha x : ℝ), 0 ≤ r → r < 1 →
      alpha ∈ Icc (0 : ℝ) 1 → x ∈ Ico (0 : ℝ) 1 →
      geometricAtomicMeasure r x (Iic alpha) =
        ENNReal.ofReal (D5.S1.Words.Mechanical.MechanicalReadoutOrder.geometricReadout r alpha x))
    distributionRealization := by
  constructor
  change (∀ (r alpha x : ℝ), 0 ≤ r → r < 1 →
      alpha ∈ Icc (0 : ℝ) 1 → x ∈ Ico (0 : ℝ) 1 →
      geometricAtomicMeasure r x (Iic alpha) =
      ENNReal.ofReal (D5.S1.Words.Mechanical.MechanicalReadoutOrder.geometricReadout r alpha x)) ↔
    distributionReadout = distributionTarget
  constructor
  · intro h
    funext input
    change MechanicalReadoutSources.distributionReadout input =
      MechanicalReadoutSources.distributionTarget input
    by_cases hc : 0 ≤ input.ratio ∧ input.ratio < 1 ∧
        input.threshold ∈ Icc (0 : ℝ) 1 ∧ input.phase ∈ Ico (0 : ℝ) 1
    · simp only [MechanicalReadoutSources.distributionTarget, if_pos hc]
      exact h input.ratio input.threshold input.phase hc.1 hc.2.1 hc.2.2.1 hc.2.2.2
    · simp only [MechanicalReadoutSources.distributionTarget, if_neg hc]
  · intro h r alpha x hr0 hr1 ha hx
    have hv := congrFun h
      (MechanicalReadoutSources.DistributionInput.mk r alpha x)
    have hc : 0 ≤ r ∧ r < 1 ∧ alpha ∈ Icc (0 : ℝ) 1 ∧
        x ∈ Ico (0 : ℝ) 1 := ⟨hr0, hr1, ha, hx⟩
    simp only [distributionReadout, distributionTarget,
      MechanicalReadoutSources.distributionTarget, if_pos hc] at hv
    change geometricAtomicMeasure r x (Iic alpha) =
      ENNReal.ofReal
        (D5.S1.Words.Mechanical.MechanicalReadoutOrder.geometricReadout r alpha x) at hv
    exact hv

private def distributionBadOutput : DistributionOutput := fun input =>
  if distributionTarget input = 0 then 1 else 0

def distributionBad := @mechanicalReadoutRealization DistributionOutput
  (Classical.decEq _) (fun _ : Unit => distributionBadOutput)

private theorem distributionBad_not_law : ¬ distributionArena.Law distributionBad := by
  intro h
  have hh := congrFun h distributionSample
  change (if distributionTarget distributionSample = 0 then 1 else 0) =
    distributionTarget distributionSample at hh
  by_cases hz : distributionTarget distributionSample = 0
  · simp [hz] at hh
  · simp only [if_neg hz] at hh
    exact hz hh.symm

theorem distributionVariation : distributionArena.Law distributionRealization ∧
    ¬ distributionArena.Law distributionBad := by
  constructor
  · exact distributionBridge.equivalence.mp
      (fun r alpha x hr0 hr1 ha hx => geometric_atomic_apply_Iic r alpha x hr0 hr1 ha hx)
  · exact distributionBad_not_law

theorem distributionSensitivity : FiniteSlotSensitivity distributionArena.toPrimitiveLawArena := by
  constructor
  · intro i
    cases i
    let good := @mechanicalReadoutRealization DistributionOutput
      (Classical.decEq _) (fun _ : Unit => distributionTarget)
    refine ⟨good, distributionBad, ?_, ?_, ?_⟩
    · intro j hj
      cases j
      exact (hj rfl).elim
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ => distributionBad_not_law, fun _ => rfl⟩
  · intro i
    exact Fin.elim0 i

theorem hitBridge : LegacyPrimitiveRealization hitArena.toPrimitiveLawArena
    (∀ (r x alpha : ℝ), x ∈ Ico (0 : ℝ) 1 → alpha ∈ Ioo (0 : ℝ) 1 →
      geometricAtomicMeasure r x {alpha} =
        ∑' n : ℕ, if ∃ z : ℤ,
            (z : ℝ) = x + (((n + 1 : ℕ) : ℝ)) * alpha then
          ENNReal.ofReal ((1 - r) ^ 2 * r ^ n) else 0)
    hitRealization := by
  constructor
  change (∀ (r x alpha : ℝ), x ∈ Ico (0 : ℝ) 1 → alpha ∈ Ioo (0 : ℝ) 1 →
      geometricAtomicMeasure r x {alpha} =
        ∑' n : ℕ, if ∃ z : ℤ,
            (z : ℝ) = x + (((n + 1 : ℕ) : ℝ)) * alpha then
        ENNReal.ofReal ((1 - r) ^ 2 * r ^ n) else 0) ↔
    hitReadout = hitTarget
  constructor
  · intro h
    funext input
    change MechanicalReadoutSources.hitReadout input =
      MechanicalReadoutSources.hitTarget input
    by_cases hc : input.phase ∈ Ico (0 : ℝ) 1 ∧
        input.threshold ∈ Ioo (0 : ℝ) 1
    · simp only [MechanicalReadoutSources.hitTarget, if_pos hc]
      exact h input.ratio input.phase input.threshold hc.1 hc.2
    · simp only [MechanicalReadoutSources.hitTarget, if_neg hc]
  · intro h r x alpha hx ha
    have hv := congrFun h (MechanicalReadoutSources.HitInput.mk r x alpha)
    have hc : x ∈ Ico (0 : ℝ) 1 ∧ alpha ∈ Ioo (0 : ℝ) 1 := ⟨hx, ha⟩
    simp only [hitReadout, hitTarget, MechanicalReadoutSources.hitTarget,
      if_pos hc] at hv
    change geometricAtomicMeasure r x {alpha} =
      ∑' n : ℕ, if ∃ z : ℤ,
          (z : ℝ) = x + (((n + 1 : ℕ) : ℝ)) * alpha then
        ENNReal.ofReal ((1 - r) ^ 2 * r ^ n) else 0 at hv
    exact hv

private def hitBadOutput : HitOutput := fun input =>
  if hitTarget input = 0 then 1 else 0

def hitBad := @mechanicalReadoutRealization HitOutput
  (Classical.decEq _) (fun _ : Unit => hitBadOutput)

private theorem hitBad_not_law : ¬ hitArena.Law hitBad := by
  intro h
  have hh := congrFun h hitSample
  change (if hitTarget hitSample = 0 then 1 else 0) = hitTarget hitSample at hh
  by_cases hz : hitTarget hitSample = 0
  · simp [hz] at hh
  · simp only [if_neg hz] at hh
    exact hz hh.symm

theorem hitVariation : hitArena.Law hitRealization ∧
    ¬ hitArena.Law hitBad := by
  constructor
  · exact hitBridge.equivalence.mp
      (fun r x alpha hx ha => geometric_atomic_singleton_hit r x alpha hx ha)
  · exact hitBad_not_law

theorem hitSensitivity : FiniteSlotSensitivity hitArena.toPrimitiveLawArena := by
  constructor
  · intro i
    cases i
    let good := @mechanicalReadoutRealization HitOutput
      (Classical.decEq _) (fun _ : Unit => hitTarget)
    refine ⟨good, hitBad, ?_, ?_, ?_⟩
    · intro j hj
      cases j
      exact (hj rfl).elim
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ => hitBad_not_law, fun _ => rfl⟩
  · intro i
    exact Fin.elim0 i

theorem supportBridge : LegacyPrimitiveRealization supportArena.toPrimitiveLawArena
    (∀ (r x : ℝ), 0 < r → r < 1 → x ∈ Ico (0 : ℝ) 1 →
      (geometricAtomicMeasure r x).support = Icc (0 : ℝ) 1)
    supportRealization := by
  constructor
  change (∀ (r x : ℝ), 0 < r → r < 1 → x ∈ Ico (0 : ℝ) 1 →
      (geometricAtomicMeasure r x).support = Icc (0 : ℝ) 1) ↔
    supportReadout = supportTarget
  constructor
  · intro h
    funext input
    change MechanicalReadoutSources.supportReadout input =
      MechanicalReadoutSources.supportTarget input
    by_cases hc : 0 < input.ratio ∧ input.ratio < 1 ∧
        input.phase ∈ Ico (0 : ℝ) 1
    · simp only [MechanicalReadoutSources.supportTarget, if_pos hc]
      exact h input.ratio input.phase hc.1 hc.2.1 hc.2.2
    · simp only [MechanicalReadoutSources.supportTarget, if_neg hc]
  · intro h r x hr0 hr1 hx
    have hv := congrFun h (MechanicalReadoutSources.SupportInput.mk r x)
    have hc : 0 < r ∧ r < 1 ∧ x ∈ Ico (0 : ℝ) 1 := ⟨hr0, hr1, hx⟩
    simp only [supportReadout, supportTarget,
      MechanicalReadoutSources.supportTarget, if_pos hc] at hv
    change (geometricAtomicMeasure r x).support = Icc (0 : ℝ) 1 at hv
    exact hv

private def supportBadOutput : SupportOutput := fun input =>
  if supportTarget input = ∅ then Set.univ else ∅

def supportBad := @mechanicalReadoutRealization SupportOutput
  (Classical.decEq _) (fun _ : Unit => supportBadOutput)

private theorem supportBad_not_law : ¬ supportArena.Law supportBad := by
  intro h
  have hh := congrFun h supportSample
  change (if supportTarget supportSample = ∅ then Set.univ else ∅) =
    supportTarget supportSample at hh
  by_cases hz : supportTarget supportSample = ∅
  · have hne : (Set.univ : Set ℝ) = ∅ := by simpa [hz] using hh
    have hmem : (0 : ℝ) ∈ (∅ : Set ℝ) := by
      rw [← hne]
      trivial
    simpa using hmem
  · simp only [if_neg hz] at hh
    exact hz hh.symm

theorem supportVariation : supportArena.Law supportRealization ∧
    ¬ supportArena.Law supportBad := by
  constructor
  · exact supportBridge.equivalence.mp
      (fun r x hr0 hr1 hx => geometric_atomic_support r x hr0 hr1 hx)
  · exact supportBad_not_law

theorem supportSensitivity : FiniteSlotSensitivity supportArena.toPrimitiveLawArena := by
  constructor
  · intro i
    cases i
    let good := @mechanicalReadoutRealization SupportOutput
      (Classical.decEq _) (fun _ : Unit => supportTarget)
    refine ⟨good, supportBad, ?_, ?_, ?_⟩
    · intro j hj
      cases j
      exact (hj rfl).elim
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ => supportBad_not_law, fun _ => rfl⟩
  · intro i
    exact Fin.elim0 i

theorem leftJumpBridge : LegacyPrimitiveRealization leftJumpArena.toPrimitiveLawArena
    (∀ (r x alpha : ℝ), 0 < r → r < 1 →
      x ∈ Ico (0 : ℝ) 1 → alpha ∈ Ioo (0 : ℝ) 1 →
      ∃ L : ℝ,
        Filter.Tendsto (fun beta : ℝ => D5.S1.Words.Mechanical.MechanicalReadoutOrder.geometricReadout r beta x)
          (𝓝[<] alpha) (𝓝 L) ∧
        L = (geometricAtomicMeasure r x (Iio alpha)).toReal ∧
        D5.S1.Words.Mechanical.MechanicalReadoutOrder.geometricReadout r alpha x - L =
          ∑' n : ℕ, if ∃ z : ℤ,
              (z : ℝ) = x + (((n + 1 : ℕ) : ℝ)) * alpha then
            (1 - r) ^ 2 * r ^ n else 0)
    jumpRealization := by
  constructor
  change (∀ (r x alpha : ℝ), 0 < r → r < 1 →
      x ∈ Ico (0 : ℝ) 1 → alpha ∈ Ioo (0 : ℝ) 1 →
      ∃ L : ℝ,
        Filter.Tendsto (fun beta : ℝ => D5.S1.Words.Mechanical.MechanicalReadoutOrder.geometricReadout r beta x)
          (𝓝[<] alpha) (𝓝 L) ∧
        L = (geometricAtomicMeasure r x (Iio alpha)).toReal ∧
        D5.S1.Words.Mechanical.MechanicalReadoutOrder.geometricReadout r alpha x - L =
          ∑' n : ℕ, if ∃ z : ℤ,
              (z : ℝ) = x + (((n + 1 : ℕ) : ℝ)) * alpha then
            (1 - r) ^ 2 * r ^ n else 0) ↔
    (∀ (r x alpha : ℝ), 0 < r → r < 1 →
      x ∈ Ico (0 : ℝ) 1 → alpha ∈ Ioo (0 : ℝ) 1 →
      ∃ L : ℝ,
        Filter.Tendsto (fun beta : ℝ => jumpRealization.readout () () r beta x)
          (𝓝[<] alpha) (𝓝 L) ∧
        L = (geometricAtomicMeasure r x (Iio alpha)).toReal ∧
        jumpRealization.readout () () r alpha x - L =
          ∑' n : ℕ, if ∃ z : ℤ,
              (z : ℝ) = x + (((n + 1 : ℕ) : ℝ)) * alpha then
            (1 - r) ^ 2 * r ^ n else 0)
  exact Iff.rfl

theorem rationalJumpBridge : LegacyPrimitiveRealization rationalJumpArena.toPrimitiveLawArena
    (∀ (r : ℝ) (p q : ℕ), 0 < r → r < 1 →
      0 < p → p < q → Nat.Coprime p q →
      ∃ L : ℝ,
        Filter.Tendsto (fun beta : ℝ => D5.S1.Words.Mechanical.MechanicalReadoutOrder.geometricReadout r beta 0)
          (𝓝[<] ((p : ℝ) / q)) (𝓝 L) ∧
        D5.S1.Words.Mechanical.MechanicalReadoutOrder.geometricReadout r ((p : ℝ) / q) 0 - L =
          (1 - r) ^ 2 * r ^ (q - 1) / (1 - r ^ q))
    jumpRealization := by
  constructor
  change (∀ (r : ℝ) (p q : ℕ), 0 < r → r < 1 →
      0 < p → p < q → Nat.Coprime p q →
      ∃ L : ℝ,
        Filter.Tendsto (fun beta : ℝ => D5.S1.Words.Mechanical.MechanicalReadoutOrder.geometricReadout r beta 0)
          (𝓝[<] ((p : ℝ) / q)) (𝓝 L) ∧
        D5.S1.Words.Mechanical.MechanicalReadoutOrder.geometricReadout r ((p : ℝ) / q) 0 - L =
          (1 - r) ^ 2 * r ^ (q - 1) / (1 - r ^ q)) ↔
    (∀ (r : ℝ) (p q : ℕ), 0 < r → r < 1 →
      0 < p → p < q → Nat.Coprime p q →
      ∃ L : ℝ,
        Filter.Tendsto (fun beta : ℝ => jumpRealization.readout () () r beta 0)
          (𝓝[<] ((p : ℝ) / q)) (𝓝 L) ∧
        jumpRealization.readout () () r ((p : ℝ) / q) 0 - L =
          (1 - r) ^ 2 * r ^ (q - 1) / (1 - r ^ q))
  exact Iff.rfl

def jumpBad := @mechanicalReadoutRealization JumpOutput (Classical.decEq _)
  (fun _ : Unit => fun _ _ _ => (0 : ℝ))

private theorem positiveHalfHitSeries :
    0 < ∑' n : ℕ, if ∃ z : ℤ,
        (z : ℝ) = (0 : ℝ) + (((n + 1 : ℕ) : ℝ)) * (1 / 2 : ℝ) then
      (1 - (1 / 2 : ℝ)) ^ 2 * (1 / 2 : ℝ) ^ n else 0 := by
  obtain ⟨L₁, hlimit₁, _, hseries⟩ :=
    geometric_readout_left_jump_exact (1 / 2) 0 (1 / 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨L₂, hlimit₂, hclosed⟩ :=
    geometric_rational_left_jump_closed_form (1 / 2) 1 2
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
  have hlimit₂' : Filter.Tendsto
      (fun beta : ℝ => D5.S1.Words.Mechanical.MechanicalReadoutOrder.geometricReadout
        (1 / 2) beta 0) (𝓝[<] (1 / 2 : ℝ)) (𝓝 L₂) := by
    simpa using hlimit₂
  have hsame : L₁ = L₂ := tendsto_nhds_unique hlimit₁ hlimit₂'
  rw [← hsame] at hclosed
  have hformula :
      (∑' n : ℕ, if ∃ z : ℤ,
          (z : ℝ) = (0 : ℝ) + (((n + 1 : ℕ) : ℝ)) * (1 / 2 : ℝ) then
        (1 - (1 / 2 : ℝ)) ^ 2 * (1 / 2 : ℝ) ^ n else 0) =
        (1 - (1 / 2 : ℝ)) ^ 2 * (1 / 2 : ℝ) ^ (2 - 1) /
          (1 - (1 / 2 : ℝ) ^ 2) := by
    linarith [hseries, hclosed]
  rw [hformula]
  norm_num

private theorem leftJumpBad_not_law : ¬ leftJumpArena.Law jumpBad := by
  intro h
  obtain ⟨L, hlimit, _, hseries⟩ := h (1 / 2) 0 (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hlimitZero : Filter.Tendsto (fun _ : ℝ => (0 : ℝ))
      (𝓝[<] (1 / 2 : ℝ)) (𝓝 L) := by
    simpa [jumpBad, mechanicalReadoutRealization] using hlimit
  have hL : L = 0 := tendsto_nhds_unique hlimitZero tendsto_const_nhds
  have hzero :
      (0 : ℝ) = ∑' n : ℕ, if ∃ z : ℤ,
          (z : ℝ) = (0 : ℝ) + (((n + 1 : ℕ) : ℝ)) * (1 / 2 : ℝ) then
        (1 - (1 / 2 : ℝ)) ^ 2 * (1 / 2 : ℝ) ^ n else 0 := by
    simpa [jumpBad, mechanicalReadoutRealization, hL] using hseries
  exact (ne_of_gt positiveHalfHitSeries) hzero.symm

private theorem rationalJumpBad_not_law : ¬ rationalJumpArena.Law jumpBad := by
  intro h
  obtain ⟨L, hlimit, hclosed⟩ := h (1 / 2) 1 2
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
  have hlimitZero : Filter.Tendsto (fun _ : ℝ => (0 : ℝ))
      (𝓝[<] (1 / 2 : ℝ)) (𝓝 L) := by
    simpa [jumpBad, mechanicalReadoutRealization] using hlimit
  have hL : L = 0 := tendsto_nhds_unique hlimitZero tendsto_const_nhds
  simp [jumpBad, mechanicalReadoutRealization, hL] at hclosed
  norm_num at hclosed

theorem leftJumpVariation : leftJumpArena.Law jumpRealization ∧
    ¬ leftJumpArena.Law jumpBad := by
  exact ⟨leftJumpBridge.equivalence.mp geometric_readout_left_jump_exact,
    leftJumpBad_not_law⟩

theorem rationalJumpVariation : rationalJumpArena.Law jumpRealization ∧
    ¬ rationalJumpArena.Law jumpBad := by
  exact ⟨rationalJumpBridge.equivalence.mp geometric_rational_left_jump_closed_form,
    rationalJumpBad_not_law⟩

theorem leftJumpSensitivity : FiniteSlotSensitivity leftJumpArena.toPrimitiveLawArena := by
  constructor
  · intro i
    cases i
    refine ⟨jumpRealization, jumpBad, ?_, ?_, ?_⟩
    · intro j hj
      cases j
      exact (hj rfl).elim
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ => leftJumpBad_not_law, fun _ => leftJumpVariation.1⟩
  · intro i
    exact Fin.elim0 i

theorem rationalJumpSensitivity : FiniteSlotSensitivity rationalJumpArena.toPrimitiveLawArena := by
  constructor
  · intro i
    cases i
    refine ⟨jumpRealization, jumpBad, ?_, ?_, ?_⟩
    · intro j hj
      cases j
      exact (hj rfl).elim
    · intro j
      exact Fin.elim0 j
    · exact ⟨fun _ => rationalJumpBad_not_law, fun _ => rationalJumpVariation.1⟩
  · intro i
    exact Fin.elim0 i

register_information_theorem
  _root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_apply_Iic
  in distributionArena
  readout via (@mechanicalReadoutRealization DistributionOutput (Classical.decEq _)
    (fun _ : Unit => MechanicalReadoutSources.distributionReadout))
  primitives distributionRealization.toPrimitiveBundle
  realization distributionBridge
  variation distributionVariation sensitivity distributionSensitivity
  escape from (ℝ) escape continues (open)

register_information_theorem
  _root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_singleton_hit
  in hitArena
  readout via (@mechanicalReadoutRealization HitOutput (Classical.decEq _)
    (fun _ : Unit => MechanicalReadoutSources.hitReadout))
  primitives hitRealization.toPrimitiveBundle
  realization hitBridge
  variation hitVariation sensitivity hitSensitivity
  escape from (ℝ) escape continues (open)

register_information_theorem
  _root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_support
  in supportArena
  readout via (@mechanicalReadoutRealization SupportOutput (Classical.decEq _)
    (fun _ : Unit => MechanicalReadoutSources.supportReadout))
  primitives supportRealization.toPrimitiveBundle
  realization supportBridge
  variation supportVariation sensitivity supportSensitivity
  escape from (ℝ) escape continues (open)

register_information_theorem
  _root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_readout_left_jump_exact
  in leftJumpArena
  readout via (@mechanicalReadoutRealization JumpOutput (Classical.decEq _)
    (fun _ : Unit => MechanicalReadoutSources.jumpReadout))
  primitives jumpRealization.toPrimitiveBundle
  realization leftJumpBridge
  variation leftJumpVariation sensitivity leftJumpSensitivity
  escape from (ℝ) escape continues (open)

register_information_theorem
  _root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_rational_left_jump_closed_form
  in rationalJumpArena
  readout via (@mechanicalReadoutRealization JumpOutput (Classical.decEq _)
    (fun _ : Unit => MechanicalReadoutSources.jumpReadout))
  primitives jumpRealization.toPrimitiveBundle
  realization rationalJumpBridge
  variation rationalJumpVariation sensitivity rationalJumpSensitivity
  escape from (ℝ) escape continues (open)

open Lean in
run_meta do
  for theoremName in #[
      `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_apply_Iic,
      `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_singleton_hit,
      `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_support,
      `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_readout_left_jump_exact,
      `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_rational_left_jump_closed_form] do
    let row := (TemplateBinding.records (← getEnv)).find? fun record =>
      record.occurrence.key.theoremName == theoremName
    let valid := row.any fun record => match record.result with
      | .declaredValidated _ => true
      | _ => false
    unless valid do throwError "atomic-measure information registration is not declaredValidated: {theoremName}"

end Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure
