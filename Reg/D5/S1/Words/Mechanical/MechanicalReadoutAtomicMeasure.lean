import Reg.Support.NodeFacts
import LeanInformationAuditInterface.Contract.NodeFacts
import Reg.Support.CompiledNodeTerm
import LeanInformationAuditInterface.Contract.Registration
import D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena
import D5.S3.ConceptDynamics.InformationEscape.TheoremUnit
import D5.S3.ConceptDynamics.RegistrationWitnesses
import D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure
import D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration
import Reg.Support.PointwiseEqualityRegistrations
import Reg.Support.MechanicalDyadicRegistration



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

theorem rationalJumpVariation : rationalJumpArena.Law jumpRealization ∧
    ¬ rationalJumpArena.Law jumpBad := by
  exact ⟨rationalJumpBridge.equivalence.mp geometric_rational_left_jump_closed_form,
    rationalJumpBad_not_law⟩

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

noncomputable def registration_1 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_apply_Iic) (type_of% (@mechanicalReadoutRealization DistributionOutput (Classical.decEq.{1} _)
    (fun _ : Unit => MechanicalReadoutSources.distributionReadout))) (type_of% (ℝ)) (Unit) := {
  unitName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_apply_Iic.__information_unit,
  realizationName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.distributionBridge,
  realizationSource := none,
  generated := false,
  arena := .object ⟨(distributionArena)⟩,
  objectArena := .object ⟨(distributionArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.toPrimitiveLawArena.{0, 0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.distributionArena) (D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.distributionRealization) (distributionRealization.toPrimitiveBundle) ⟨(distributionBridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (distributionBridge) (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_apply_Iic))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((distributionRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@mechanicalReadoutRealization DistributionOutput (Classical.decEq.{1} _)
    (fun _ : Unit => MechanicalReadoutSources.distributionReadout)),
  variation := .evidence ⟨(distributionVariation)⟩ (by first | exact (distributionVariation) | exact ⟨_, _, (distributionVariation)⟩),
  sensitivity := .evidence ⟨(distributionSensitivity)⟩ (by exact (distributionSensitivity)),
  partialSensitivity := none,
  escapeFrom := some (ℝ),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxHeartbeats, value := .nat 2000000 }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_apply_Iic, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_1.canonicalArenaFact, `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_1.canonicalObjectArenaFact] },
  exclusion := none,
  finiteLift := none,
  roleEnumeration := none,
  anchorEnumeration := none }


noncomputable def registration_2 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_singleton_hit) (type_of% (@mechanicalReadoutRealization HitOutput (Classical.decEq.{1} _)
    (fun _ : Unit => MechanicalReadoutSources.hitReadout))) (type_of% (ℝ)) (Unit) := {
  unitName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_singleton_hit.__information_unit,
  realizationName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.hitBridge,
  realizationSource := none,
  generated := false,
  arena := .object ⟨(hitArena)⟩,
  objectArena := .object ⟨(hitArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.toPrimitiveLawArena.{0, 0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.hitArena) (D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.hitRealization) (hitRealization.toPrimitiveBundle) ⟨(hitBridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (hitBridge) (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_singleton_hit))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((hitRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@mechanicalReadoutRealization HitOutput (Classical.decEq.{1} _)
    (fun _ : Unit => MechanicalReadoutSources.hitReadout)),
  variation := .evidence ⟨(hitVariation)⟩ (by first | exact (hitVariation) | exact ⟨_, _, (hitVariation)⟩),
  sensitivity := .evidence ⟨(hitSensitivity)⟩ (by exact (hitSensitivity)),
  partialSensitivity := none,
  escapeFrom := some (ℝ),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxHeartbeats, value := .nat 2000000 }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_singleton_hit, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_2.canonicalArenaFact, `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_2.canonicalObjectArenaFact] },
  exclusion := none,
  finiteLift := none,
  roleEnumeration := none,
  anchorEnumeration := none }


noncomputable def registration_3 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_support) (type_of% (@mechanicalReadoutRealization SupportOutput (Classical.decEq.{1} _)
    (fun _ : Unit => MechanicalReadoutSources.supportReadout))) (type_of% (ℝ)) (Unit) := {
  unitName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_support.__information_unit,
  realizationName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.supportBridge,
  realizationSource := none,
  generated := false,
  arena := .object ⟨(supportArena)⟩,
  objectArena := .object ⟨(supportArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.toPrimitiveLawArena.{0, 0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.supportArena) (D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.supportRealization) (supportRealization.toPrimitiveBundle) ⟨(supportBridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (supportBridge) (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_support))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((supportRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@mechanicalReadoutRealization SupportOutput (Classical.decEq.{1} _)
    (fun _ : Unit => MechanicalReadoutSources.supportReadout)),
  variation := .evidence ⟨(supportVariation)⟩ (by first | exact (supportVariation) | exact ⟨_, _, (supportVariation)⟩),
  sensitivity := .evidence ⟨(supportSensitivity)⟩ (by exact (supportSensitivity)),
  partialSensitivity := none,
  escapeFrom := some (ℝ),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxHeartbeats, value := .nat 2000000 }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_atomic_support, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_3.canonicalArenaFact, `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_3.canonicalObjectArenaFact] },
  exclusion := none,
  finiteLift := none,
  roleEnumeration := none,
  anchorEnumeration := none }


noncomputable def registration_4 : LeanInformationAudit.Contract.Registration.{_,_,_,_,_,_,0,0,0,0,0,0} (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_rational_left_jump_closed_form) (type_of% (@mechanicalReadoutRealization JumpOutput (Classical.decEq.{1} _)
    (fun _ : Unit => MechanicalReadoutSources.jumpReadout))) (type_of% (ℝ)) (Unit) := {
  unitName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_rational_left_jump_closed_form.__information_unit,
  realizationName := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.rationalJumpBridge,
  realizationSource := none,
  generated := false,
  arena := .object ⟨(rationalJumpArena)⟩,
  objectArena := .object ⟨(rationalJumpArena)⟩,
  catalog := Lean.Name.anonymous,
  localNames := true,
  realization := .legacy (D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.toPrimitiveLawArena.{0, 0, 0, 0} D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.rationalJumpArena) (D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.jumpRealization) (jumpRealization.toPrimitiveBundle) ⟨(rationalJumpBridge)⟩ (.evidence) { value := ⟨(_root_.D5.S3.ConceptDynamics.InformationEscape.LegacyPrimitiveRealization.toTheoremUnit (rationalJumpBridge) (@_root_.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_rational_left_jump_closed_form))⟩, statement := .evidence, bundle := .evidence },
  correspondence := { stage := .evidence, objectStage := .evidence },
  bundleNonempty := .evidence ⟨(by trivial : True)⟩ (by change ((jumpRealization.toPrimitiveBundle)).Nonempty; decide),
  readout := some (@mechanicalReadoutRealization JumpOutput (Classical.decEq.{1} _)
    (fun _ : Unit => MechanicalReadoutSources.jumpReadout)),
  variation := .evidence ⟨(rationalJumpVariation)⟩ (by first | exact (rationalJumpVariation) | exact ⟨_, _, (rationalJumpVariation)⟩),
  sensitivity := .evidence ⟨(rationalJumpSensitivity)⟩ (by exact (rationalJumpSensitivity)),
  partialSensitivity := none,
  escapeFrom := some (ℝ),
  sourceSelection := none,
  continuation := .unknown,
  familyRecord := none,
  options := #[{ name := `Elab.async, value := .bool true }, { name := `autoImplicit, value := .bool false }, { name := `internal.cmdlineSnapshots, value := .bool true }, { name := `linter.mathlibStandardSet, value := .bool true }, { name := `maxHeartbeats, value := .nat 2000000 }, { name := `maxSynthPendingDepth, value := .nat 3 }, { name := `pp.unicode.fun, value := .bool true }, { name := `relaxedAutoImplicit, value := .bool false }],
  coverage := { roots := [
    { owner := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.geometric_rational_left_jump_closed_form, part := .type, path := [], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument], levels := [] },
    { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument], levels := [] }], facts := [`Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_4.canonicalArenaFact, `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_4.canonicalObjectArenaFact] },
  exclusion := none,
  finiteLift := none,
  roleEnumeration := none,
  anchorEnumeration := none }


end Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure


noncomputable def Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_3.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.{0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.supportArena
noncomputable def Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_3.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"MechanicalReadoutAtomicMeasure\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"MechanicalReadoutAtomicMeasure\",\"registration_3\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_3.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_3.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.{0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.supportArena
noncomputable def Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_3.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"MechanicalReadoutAtomicMeasure\",\"registration_3\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"MechanicalReadoutAtomicMeasure\",\"registration_3\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_3, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_3.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_4.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.{0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.rationalJumpArena
noncomputable def Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_4.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"MechanicalReadoutAtomicMeasure\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"MechanicalReadoutAtomicMeasure\",\"registration_4\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_4.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_4.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.{0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.rationalJumpArena
noncomputable def Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_4.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"MechanicalReadoutAtomicMeasure\",\"registration_4\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"MechanicalReadoutAtomicMeasure\",\"registration_4\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_4, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_4.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_2.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.{0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.hitArena
noncomputable def Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_2.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"MechanicalReadoutAtomicMeasure\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"MechanicalReadoutAtomicMeasure\",\"registration_2\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_2.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_2.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.{0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.hitArena
noncomputable def Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_2.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"MechanicalReadoutAtomicMeasure\",\"registration_2\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"MechanicalReadoutAtomicMeasure\",\"registration_2\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_2, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_2.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence

noncomputable def Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_1.canonicalArenaOperand : D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.{0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.distributionArena
noncomputable def Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_1.canonicalArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"MechanicalReadoutAtomicMeasure\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"MechanicalReadoutAtomicMeasure\",\"registration_1\",\"canonicalArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_1.canonicalArenaOperand, part := .value, path := [], levels := [] }
  .evidence
noncomputable def Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_1.canonicalObjectArenaOperand : D5.S3.ConceptDynamics.InformationEscape.ObjectDomainArena.{0, 0, 0, 0} :=
  D5.S3.ConceptDynamics.InformationEscape.MechanicalAtomicMeasureRegistration.distributionArena
noncomputable def Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_1.canonicalObjectArenaFact : LeanInformationAudit.Contract.NodeFact := .exact
  (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"MechanicalReadoutAtomicMeasure\",\"registration_1\"],\"part\":\"value\",\"path\":[\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"function\",\"argument\",\"argument\",\"argument\"],\"levels\":[]}")) (@(compiled_node% "{\"declaration\":[\"Reg\",\"D5\",\"S1\",\"Words\",\"Mechanical\",\"MechanicalReadoutAtomicMeasure\",\"registration_1\",\"canonicalObjectArenaOperand\"],\"part\":\"value\",\"path\":[],\"levels\":[]}"))
  { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_1, part := .value, path := [.function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .function, .argument, .argument, .argument], levels := [] }
  { owner := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure, declaration := `Reg.D5.S1.Words.Mechanical.MechanicalReadoutAtomicMeasure.registration_1.canonicalObjectArenaOperand, part := .value, path := [], levels := [] }
  .evidence
