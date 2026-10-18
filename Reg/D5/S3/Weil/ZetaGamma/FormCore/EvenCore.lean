/- SOURCE_ONLY_UNCOMPILED. Source pins and faithful attempt inventory, not validated registrations. -/
import D5.S3.Weil.ZetaGamma.FormCore.EvenCore
import Reg.Support.DependentFamily
import LeanInformationAuditInterface.Contract.Registration
import Reg.Support.SingleDependentReadout

namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.EvenCore

-- Two actual complete-candidate Boolean dependent-family attempts below retain the full hypotheses, strict support and both graph-error variants. They include explicit accept/reject variation, fixed-other-role sensitivity and observational dependence. Their exact raw source coordinate selection (a,u,epsilon; existential g as state, with whole-line let F expansion) has deliberately not been guessed; no Contract.Registration or compiled binding evidence is claimed for these two attempts.
def source_actual_ioc_exists_weil_test_core_approximation := @_root_.D5.S3.Weil.ZetaGamma.FormCore.actual_ioc_exists_weil_test_core_approximation

-- Two actual complete-candidate Boolean dependent-family attempts below retain the full hypotheses, strict support and both graph-error variants. They include explicit accept/reject variation, fixed-other-role sensitivity and observational dependence. Their exact raw source coordinate selection (a,u,epsilon; existential g as state, with whole-line let F expansion) has deliberately not been guessed; no Contract.Registration or compiled binding evidence is claimed for these two attempts.
def source_actual_ioc_exists_weil_test_core_approximation_on_source := @_root_.D5.S3.Weil.ZetaGamma.FormCore.actual_ioc_exists_weil_test_core_approximation_on_source

end Reg.D5.S3.Weil.ZetaGamma.FormCore.EvenCore
open MeasureTheory Set Filter
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open _root_.D5.S3.Weil.ZetaGamma.FormCore
open _root_.D5.S3.Weil.TestFunctions
open scoped ENNReal Classical

noncomputable section
namespace Reg.D5.S3.Weil.ZetaGamma.FormCore.EvenCore

private def zeroTest : WeilTestFunction where
  toFun := fun _ => 0
  contDiff' := contDiff_const
  hasCompactSupport' := by simp [HasCompactSupport]
  even' _ := rfl

abbrev params := ℝ × (ℝ → ℂ) × ℝ
abbrev signature := Reg.Support.SingleDependentReadout.signature params (fun _ => WeilTestFunction) (fun _ => Bool)

namespace WholeLine
def accepts (p : params) (g : WeilTestFunction) : Prop :=
  tsupport (g : ℝ → ℂ) ⊆ Ioo (-p.1) p.1 ∧
    coreL2Mass (fun x => g x - D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * p.1) (-p.1) p.2.1 x) +
      directionalEnergy actualGammaExitMeasure (fun x => g x - D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * p.1) (-p.1) p.2.1 x) < ENNReal.ofReal p.2.2

def statement : Prop :=
  ∀ (a : ℝ) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a)))
    (henergy : directionalEnergy actualGammaExitMeasure
      (D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u) < (⊤ : ℝ≥0∞))
    (heven : ∀ᵐ x : ℝ ∂volume,
      D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u (-x) =
        D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u x)
    (ε : ℝ) (hε : 0 < ε),
    let F := D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u
        ∃ g : D5.S3.Weil.TestFunctions.WeilTestFunction,
          tsupport (g : ℝ → ℂ) ⊆ Ioo (-a) a ∧
          coreL2Mass (fun x => g x - F x) +
            directionalEnergy actualGammaExitMeasure (fun x => g x - F x) <
              ENNReal.ofReal ε

def actual : Realization signature :=
  realize signature (fun _ p g => decide (accepts p g)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (a : ℝ) (u : ℝ → ℂ),
    MemLp u 2 (volume.restrict (Ioc (-a) a)) →
    directionalEnergy actualGammaExitMeasure (D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u) < (⊤ : ℝ≥0∞) →
    (∀ᵐ x : ℝ ∂volume, D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u (-x) = D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u x) →
    ∀ (ε : ℝ), 0 < ε → ∃ g : WeilTestFunction, R.readout () ⟨a, u, ε⟩ g = true

theorem bridge : statement ↔ arena.Law actual := by
  simp only [statement, arena, actual, realize, accepts, decide_eq_true_eq]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hu0 : MemLp (fun _ : ℝ => (0 : ℂ)) 2 (volume.restrict (Ioc (-(0 : ℝ)) 0)) := memLp_zero
  have hE0 : directionalEnergy actualGammaExitMeasure
      (D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * 0) (-0) (fun _ : ℝ => (0 : ℂ))) < (⊤ : ℝ≥0∞) := by
    simp [D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension, directionalEnergy]
  have heven0 : ∀ᵐ x : ℝ ∂volume,
      D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * 0) (-0) (fun _ : ℝ => (0 : ℂ)) (-x) =
        D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * 0) (-0) (fun _ : ℝ => (0 : ℂ)) x := by
    simp [D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension]
  obtain ⟨g, hg⟩ := h 0 (fun _ => 0) hu0 hE0 heven0 1 (by norm_num)
  change false = true at hg
  exact Bool.false_ne_true hg

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  let p : params := ⟨0, (fun _ => 0), 1⟩
  have hzero : accepts p zeroTest := by
    simp [accepts, p, zeroTest, coreL2Mass, directionalEnergy, D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension]
  have hstandard : ¬ accepts p standardTestFunction := by
    intro h
    have hmem : (0 : ℝ) ∈ tsupport (standardTestFunction : ℝ → ℂ) :=
      subset_tsupport _ (by simp)
    have hx := h.1 hmem
    change -(0 : ℝ) < 0 ∧ 0 < 0 at hx
    exact (lt_irrefl (0 : ℝ)) hx.2
  refine ⟨p, zeroTest, standardTestFunction, ?_⟩
  change decide (accepts p zeroTest) ≠ decide (accepts p standardTestFunction)
  simp [hzero, hstandard]

def registration : Registration arena statement where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (show statement from @_root_.D5.S3.Weil.ZetaGamma.FormCore.actual_ioc_exists_weil_test_core_approximation), rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := actual_dependence

-- The exact witness predicate and all original hypotheses are retained above.
-- No Contract.Registration is fabricated. Required next binding: original a,u,epsilon
-- coordinates, existential g as the actual state, and the complete support/error predicate;
-- WholeLine additionally contains source-local let F. The shared enrollment is realize,
-- but raw source reconstruction and Boolean-predicate admissibility remain unverified.
end WholeLine

namespace OnSource
def accepts (p : params) (g : WeilTestFunction) : Prop :=
  tsupport (g : ℝ → ℂ) ⊆ Ioo (-p.1) p.1 ∧
    (∫⁻ x in Ioc (-p.1) p.1, ‖g x - p.2.1 x‖ₑ ^ 2) +
      directionalEnergy actualGammaExitMeasure (fun x => g x - D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * p.1) (-p.1) p.2.1 x) < ENNReal.ofReal p.2.2

def statement : Prop :=
  ∀ (a : ℝ) (u : ℝ → ℂ)
    (hu : MemLp u 2 (volume.restrict (Ioc (-a) a)))
    (henergy : directionalEnergy actualGammaExitMeasure
      (D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u) < (⊤ : ℝ≥0∞))
    (heven : ∀ᵐ x : ℝ ∂volume,
      D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u (-x) =
        D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u x)
    (ε : ℝ) (hε : 0 < ε),
    ∃ g : D5.S3.Weil.TestFunctions.WeilTestFunction,
          tsupport (g : ℝ → ℂ) ⊆ Ioo (-a) a ∧
          (∫⁻ x in Ioc (-a) a, ‖g x - u x‖ₑ ^ 2) +
            directionalEnergy actualGammaExitMeasure
              (fun x => g x - D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u x) <
                ENNReal.ofReal ε

def actual : Realization signature :=
  realize signature (fun _ p g => decide (accepts p g)) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => false) (fun e => nomatch e)
def arena : Arena where
  signature := signature
  Law R := ∀ (a : ℝ) (u : ℝ → ℂ),
    MemLp u 2 (volume.restrict (Ioc (-a) a)) →
    directionalEnergy actualGammaExitMeasure (D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u) < (⊤ : ℝ≥0∞) →
    (∀ᵐ x : ℝ ∂volume, D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u (-x) = D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * a) (-a) u x) →
    ∀ (ε : ℝ), 0 < ε → ∃ g : WeilTestFunction, R.readout () ⟨a, u, ε⟩ g = true

theorem bridge : statement ↔ arena.Law actual := by
  simp only [statement, arena, actual, realize, accepts, decide_eq_true_eq]

theorem rejected_law : ¬ arena.Law rejected := by
  intro h
  have hu0 : MemLp (fun _ : ℝ => (0 : ℂ)) 2 (volume.restrict (Ioc (-(0 : ℝ)) 0)) := memLp_zero
  have hE0 : directionalEnergy actualGammaExitMeasure
      (D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * 0) (-0) (fun _ : ℝ => (0 : ℂ))) < (⊤ : ℝ≥0∞) := by
    simp [D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension, directionalEnergy]
  have heven0 : ∀ᵐ x : ℝ ∂volume,
      D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * 0) (-0) (fun _ : ℝ => (0 : ℂ)) (-x) =
        D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension (2 * 0) (-0) (fun _ : ℝ => (0 : ℂ)) x := by
    simp [D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension]
  obtain ⟨g, hg⟩ := h 0 (fun _ => 0) hu0 hE0 heven0 1 (by norm_num)
  change false = true at hg
  exact Bool.false_ne_true hg

theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  let p : params := ⟨0, (fun _ => 0), 1⟩
  have hzero : accepts p zeroTest := by
    simp [accepts, p, zeroTest, coreL2Mass, directionalEnergy, D5.S3.Weil.ZetaGamma.PeriodicEnergyTransport.zeroExtension]
  have hstandard : ¬ accepts p standardTestFunction := by
    intro h
    have hmem : (0 : ℝ) ∈ tsupport (standardTestFunction : ℝ → ℂ) :=
      subset_tsupport _ (by simp)
    have hx := h.1 hmem
    change -(0 : ℝ) < 0 ∧ 0 < 0 at hx
    exact (lt_irrefl (0 : ℝ)) hx.2
  refine ⟨p, zeroTest, standardTestFunction, ?_⟩
  change decide (accepts p zeroTest) ≠ decide (accepts p standardTestFunction)
  simp [hzero, hstandard]

def registration : Registration arena statement where
  actual := actual
  bridge := bridge
  variation := ⟨bridge.mp (show statement from @_root_.D5.S3.Weil.ZetaGamma.FormCore.actual_ioc_exists_weil_test_core_approximation_on_source), rejected, rejected_law⟩
  sensitivity := Reg.Support.SingleDependentReadout.sensitivity arena.Law actual rejected rejected_law
  dependence := actual_dependence

-- The exact witness predicate and all original hypotheses are retained above.
-- No Contract.Registration is fabricated. Required next binding: original a,u,epsilon
-- coordinates, existential g as the actual state, and the complete support/error predicate;
-- WholeLine additionally contains source-local let F. The shared enrollment is realize,
-- but raw source reconstruction and Boolean-predicate admissibility remain unverified.
end OnSource

end Reg.D5.S3.Weil.ZetaGamma.FormCore.EvenCore
