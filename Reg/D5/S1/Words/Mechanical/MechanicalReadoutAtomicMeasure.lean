import LeanInformationAudit.Syntax
import D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure
import D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration
import Reg.Support.MechanicalPhaseAverageRegistration
import Reg.Support.MechanicalDyadicRegistration

run_cmd LeanInformationAudit.RootCatalogs.declare {
  rootId := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure
  expected := #[
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.massArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_probability_and_carrier,
      statementIdentity := "sha256:83198120d726aa38d32ede4edb29e664caa0f838217ffd12a0e9a79cb93c3e2c",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure },
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
    { objectArenaName := `D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.massArena,
      theoremName := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_probability_and_carrier,
      statementIdentity := "sha256:83198120d726aa38d32ede4edb29e664caa0f838217ffd12a0e9a79cb93c3e2c",
      registrationModuleName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure },
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

local instance : DecidableEq MassOutput := Classical.decEq _
local instance : DecidableEq DistributionOutput := Classical.decEq _
local instance : DecidableEq HitOutput := Classical.decEq _
local instance : DecidableEq SupportOutput := Classical.decEq _
local instance : DecidableEq JumpOutput := Classical.decEq _
local instance : DecidableEq massArena.State := massArena.toArena.stateDecidableEq
local instance : DecidableEq distributionArena.State := distributionArena.toArena.stateDecidableEq
local instance : DecidableEq hitArena.State := hitArena.toArena.stateDecidableEq
local instance : DecidableEq supportArena.State := supportArena.toArena.stateDecidableEq

private def massSample : MassInput where
  ratio := 0
  phase := 0
  ratioNonnegative := le_refl 0
  ratioBelowOne := by norm_num
  phaseInUnit := by norm_num

private def distributionSample : DistributionInput where
  ratio := 0
  threshold := 0
  phase := 0
  ratioNonnegative := le_refl 0
  ratioBelowOne := by norm_num
  thresholdInUnit := by norm_num
  phaseInUnit := by norm_num

private def hitSample : HitInput where
  ratio := 0
  phase := 0
  threshold := 1 / 2
  phaseInUnit := by norm_num
  thresholdInterior := by norm_num

private def supportSample : SupportInput where
  ratio := 1 / 2
  phase := 0
  ratioPositive := by norm_num
  ratioBelowOne := by norm_num
  phaseInUnit := by norm_num

theorem massBridge : LegacyPrimitiveRealization massArena.toPrimitiveLawArena
    (∀ (r x : ℝ), 0 ≤ r → r < 1 → x ∈ Ico (0 : ℝ) 1 →
      IsProbabilityMeasure (geometricAtomicMeasure r x) ∧
      geometricAtomicMeasure r x (Ioc (0 : ℝ) 1) = 1)
    massRealization := by
  constructor
  change (∀ (r x : ℝ), 0 ≤ r → r < 1 → x ∈ Ico (0 : ℝ) 1 →
      IsProbabilityMeasure (geometricAtomicMeasure r x) ∧
      geometricAtomicMeasure r x (Ioc (0 : ℝ) 1) = 1) ↔
    (∀ _ : Unit, massReadout = massTarget)
  constructor
  · intro h _
    funext input
    obtain ⟨hprob, hcarrier⟩ := h input.ratio input.phase
      input.ratioNonnegative input.ratioBelowOne input.phaseInUnit
    exact Prod.ext (isProbabilityMeasure_iff.mp hprob) hcarrier
  · intro h r x hr0 hr1 hx
    have hv := congrFun (h ())
      (MassInput.mk r x hr0 hr1 hx)
    constructor
    · apply isProbabilityMeasure_iff.mpr
      simpa [massReadout, massTarget] using congrArg Prod.fst hv
    · simpa [massReadout, massTarget] using congrArg Prod.snd hv

private def massZero : MassOutput := fun _ => (0, 0)
private def massOne : MassOutput := fun _ => (1, 1)

private theorem massZero_ne_one : massZero ≠ massOne := by
  intro h
  have hh := congrArg Prod.fst (congrFun h massSample)
  exact zero_ne_one hh

def massBad := @homogeneousPointwiseEqRealization Unit MassOutput
  (Classical.decEq _) (fun _ => massZero) (fun _ => massOne)

theorem massVariation : massArena.Law massRealization ∧
    ¬ massArena.Law massBad := by
  constructor
  · exact massBridge.equivalence.mp
      (fun r x hr0 hr1 hx => geometric_atomic_probability_and_carrier r x hr0 hr1 hx)
  · intro h
    exact massZero_ne_one (h ())

theorem massSensitivity : FiniteSlotSensitivity massArena.toPrimitiveLawArena := by
  exact homogeneousPointwiseEq_sensitivity (Arena.ofFintype Unit)
    (x := ()) (a := massZero) (b := massOne) massZero_ne_one

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
    (∀ _ : Unit, distributionReadout = distributionTarget)
  constructor
  · intro h _
    funext input
    exact h input.ratio input.threshold input.phase input.ratioNonnegative
      input.ratioBelowOne input.thresholdInUnit input.phaseInUnit
  · intro h r alpha x hr0 hr1 ha hx
    exact congrFun (h ()) (DistributionInput.mk r alpha x hr0 hr1 ha hx)

private def distributionZero : DistributionOutput := fun _ => 0
private def distributionOne : DistributionOutput := fun _ => 1

private theorem distributionZero_ne_one : distributionZero ≠ distributionOne := by
  intro h
  exact zero_ne_one (congrFun h distributionSample)

def distributionBad := @homogeneousPointwiseEqRealization Unit DistributionOutput
  (Classical.decEq _) (fun _ => distributionZero) (fun _ => distributionOne)

theorem distributionVariation : distributionArena.Law distributionRealization ∧
    ¬ distributionArena.Law distributionBad := by
  constructor
  · exact distributionBridge.equivalence.mp
      (fun r alpha x hr0 hr1 ha hx => geometric_atomic_apply_Iic r alpha x hr0 hr1 ha hx)
  · intro h
    exact distributionZero_ne_one (h ())

theorem distributionSensitivity : FiniteSlotSensitivity distributionArena.toPrimitiveLawArena := by
  exact homogeneousPointwiseEq_sensitivity (Arena.ofFintype Unit)
    (x := ()) (a := distributionZero) (b := distributionOne) distributionZero_ne_one

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
    (∀ _ : Unit, hitReadout = hitTarget)
  constructor
  · intro h _
    funext input
    exact h input.ratio input.phase input.threshold input.phaseInUnit
      input.thresholdInterior
  · intro h r x alpha hx ha
    exact congrFun (h ()) (HitInput.mk r x alpha hx ha)

private def hitZero : HitOutput := fun _ => 0
private def hitOne : HitOutput := fun _ => 1

private theorem hitZero_ne_one : hitZero ≠ hitOne := by
  intro h
  exact zero_ne_one (congrFun h hitSample)

def hitBad := @homogeneousPointwiseEqRealization Unit HitOutput
  (Classical.decEq _) (fun _ => hitZero) (fun _ => hitOne)

theorem hitVariation : hitArena.Law hitRealization ∧
    ¬ hitArena.Law hitBad := by
  constructor
  · exact hitBridge.equivalence.mp
      (fun r x alpha hx ha => geometric_atomic_singleton_hit r x alpha hx ha)
  · intro h
    exact hitZero_ne_one (h ())

theorem hitSensitivity : FiniteSlotSensitivity hitArena.toPrimitiveLawArena := by
  exact homogeneousPointwiseEq_sensitivity (Arena.ofFintype Unit)
    (x := ()) (a := hitZero) (b := hitOne) hitZero_ne_one

theorem supportBridge : LegacyPrimitiveRealization supportArena.toPrimitiveLawArena
    (∀ (r x : ℝ), 0 < r → r < 1 → x ∈ Ico (0 : ℝ) 1 →
      (geometricAtomicMeasure r x).support = Icc (0 : ℝ) 1)
    supportRealization := by
  constructor
  change (∀ (r x : ℝ), 0 < r → r < 1 → x ∈ Ico (0 : ℝ) 1 →
      (geometricAtomicMeasure r x).support = Icc (0 : ℝ) 1) ↔
    (∀ _ : Unit, supportReadout = supportTarget)
  constructor
  · intro h _
    funext input
    exact h input.ratio input.phase input.ratioPositive input.ratioBelowOne
      input.phaseInUnit
  · intro h r x hr0 hr1 hx
    exact congrFun (h ()) (SupportInput.mk r x hr0 hr1 hx)

private def supportEmpty : SupportOutput := fun _ => ∅
private def supportFull : SupportOutput := fun _ => Set.univ

private theorem supportEmpty_ne_full : supportEmpty ≠ supportFull := by
  intro h
  have hh := congrFun h supportSample
  have hmem : (0 : ℝ) ∈ supportFull supportSample := Set.mem_univ _
  rw [← hh] at hmem
  exact Set.not_mem_empty _ hmem

def supportBad := @homogeneousPointwiseEqRealization Unit SupportOutput
  (Classical.decEq _) (fun _ => supportEmpty) (fun _ => supportFull)

theorem supportVariation : supportArena.Law supportRealization ∧
    ¬ supportArena.Law supportBad := by
  constructor
  · exact supportBridge.equivalence.mp
      (fun r x hr0 hr1 hx => geometric_atomic_support r x hr0 hr1 hx)
  · intro h
    exact supportEmpty_ne_full (h ())

theorem supportSensitivity : FiniteSlotSensitivity supportArena.toPrimitiveLawArena := by
  exact homogeneousPointwiseEq_sensitivity (Arena.ofFintype Unit)
    (x := ()) (a := supportEmpty) (b := supportFull) supportEmpty_ne_full

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
  have hsame : L₁ = L₂ := tendsto_nhds_unique hlimit₁ hlimit₂
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
  _root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_probability_and_carrier
  in massArena
  readout via (@homogeneousPointwiseEqRealization Unit MassOutput (Classical.decEq _)
    (fun _ : Unit => massReadout) (fun _ : Unit => massTarget))
  primitives massRealization.toPrimitiveBundle
  realization massBridge
  variation massVariation sensitivity massSensitivity
  escape from (ℝ) escape continues (open)

register_information_theorem
  _root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_apply_Iic
  in distributionArena
  readout via (@homogeneousPointwiseEqRealization Unit DistributionOutput (Classical.decEq _)
    (fun _ : Unit => distributionReadout) (fun _ : Unit => distributionTarget))
  primitives distributionRealization.toPrimitiveBundle
  realization distributionBridge
  variation distributionVariation sensitivity distributionSensitivity
  escape from (ℝ) escape continues (open)

register_information_theorem
  _root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_singleton_hit
  in hitArena
  readout via (@homogeneousPointwiseEqRealization Unit HitOutput (Classical.decEq _)
    (fun _ : Unit => hitReadout) (fun _ : Unit => hitTarget))
  primitives hitRealization.toPrimitiveBundle
  realization hitBridge
  variation hitVariation sensitivity hitSensitivity
  escape from (ℝ) escape continues (open)

register_information_theorem
  _root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_support
  in supportArena
  readout via (@homogeneousPointwiseEqRealization Unit SupportOutput (Classical.decEq _)
    (fun _ : Unit => supportReadout) (fun _ : Unit => supportTarget))
  primitives supportRealization.toPrimitiveBundle
  realization supportBridge
  variation supportVariation sensitivity supportSensitivity
  escape from (ℝ) escape continues (open)

register_information_theorem
  _root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_readout_left_jump_exact
  in leftJumpArena
  readout via (@mechanicalReadoutRealization JumpOutput (Classical.decEq _) jumpReadout)
  primitives jumpRealization.toPrimitiveBundle
  realization leftJumpBridge
  variation leftJumpVariation sensitivity leftJumpSensitivity
  escape from (ℝ) escape continues (open)

register_information_theorem
  _root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_rational_left_jump_closed_form
  in rationalJumpArena
  readout via (@mechanicalReadoutRealization JumpOutput (Classical.decEq _) jumpReadout)
  primitives jumpRealization.toPrimitiveBundle
  realization rationalJumpBridge
  variation rationalJumpVariation sensitivity rationalJumpSensitivity
  escape from (ℝ) escape continues (open)

open Lean in
run_meta do
  for theoremName in #[
      `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_probability_and_carrier,
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
