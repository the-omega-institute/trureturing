import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.TraceClass.ContinuousEnergyHamiltonian
import Reg.D5.S3.Quantum.Analysis.TraceClass.HellingerEnergy
import Reg.Support.SingleDependentReadout

open Filter Set
open scoped ComplexOrder InnerProductSpace ENNReal NNReal Topology BigOperators
open QuantumLogEnergy
open _root_.D5.S3.Quantum.Analysis
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.D5.S3.Quantum.Analysis.TraceClass.HellingerEnergy (K oneState one_trace one_entropy)
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace Reg.D5.S3.Quantum.Analysis.TraceClass.ContinuousEnergyHamiltonian

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)
def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)
def rejected : Realization signature :=
  realize signature (fun _ _ _ => 0) (fun e => nomatch e)

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

private def Aone : Set (TraceClass K) := {oneState.1}
private theorem Aone_positive : ∀ rho ∈ Aone, 0 ≤ rho.1 := by
  intro rho hr
  obtain rfl := Set.mem_singleton_iff.mp hr
  exact oneState.2.1
private theorem Aone_trace : ∀ rho ∈ Aone, (trace rho.1 (TraceClass.isTraceClass_coe rho)).re = 1 := by
  intro rho hr
  obtain rfl := Set.mem_singleton_iff.mp hr
  exact one_trace
private theorem Aone_entropy : ∀ (rho) (hr : rho ∈ Aone), spectralEntropy
    (⟨rho, Aone_positive rho hr, density_le_one rho (Aone_positive rho hr) (Aone_trace rho hr)⟩ : Reference K) ≠ ∞ := by
  intro rho hr
  obtain rfl := Set.mem_singleton_iff.mp hr
  change spectralEntropy oneState ≠ ∞
  rw [one_entropy]
  exact ENNReal.zero_ne_top

namespace Conditional
def arena : Arena where
  signature := signature
  Law R := ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] (sigma : Reference H)
    (htrace : (trace sigma.1.1 (TraceClass.isTraceClass_coe sigma.1)).re = 1)
    (r : SpectralResolution sigma) {A : Set (TraceClass H)}
    (hne : A.Nonempty) (hA : IsCompact A)
    (hp : ∀ rho ∈ A, 0 ≤ rho.1)
    (ht : ∀ rho ∈ A, (trace rho.1 (TraceClass.isTraceClass_coe rho)).re = 1)
    (hf : ∀ rho ∈ A, spectralEnergy sigma rho < ∞)
    (hc : ContinuousOn (fun rho => (spectralEnergy sigma rho).toReal) A)
    (δ : ℝ≥0) (hδ : 0 < δ),
       ∃ code : r.index → ℕ, Function.Injective code ∧
      ∃ w : ℕ → ℕ, (∀ n, 1 ≤ w n) ∧ Monotone w ∧ Tendsto w atTop atTop ∧
      ∃ (h : r.index → ℝ) (hh : ∀ i, 0 ≤ h i),
        (∀ i, h i = 1 + (w (code i) : ℝ) * thermalBaseLevel r code i) ∧
        ThermalOn r.basis h hh A ∧
        ∀ rho ∈ A,
          DiagonalEnergy.stateEnergy r.basis h hh rho.1 (TraceClass.isTraceClass_coe rho) =
            1 + ∑' i, ENNReal.ofReal
              ((w (code i) : ℝ) * thermalBaseLevel r code i * diagonal r.basis rho i) ∧
          DiagonalEnergy.stateEnergy r.basis h hh rho.1 (TraceClass.isTraceClass_coe rho) ≤
            1 + spectralEnergy sigma rho + (δ : ℝ≥0∞) ∧
          (DiagonalEnergy.stateEnergy r.basis h hh rho.1
            (TraceClass.isTraceClass_coe rho)).toReal ≤
            R.readout () () (1 + (spectralEnergy sigma rho).toReal + (δ : ℝ))

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro q
  have henergy : ∀ rho ∈ Aone, spectralEnergy oneState rho < ∞ := by
    intro rho hr
    obtain rfl := Set.mem_singleton_iff.mp hr
    rw [spectralEnergy_self, one_entropy]
    exact ENNReal.zero_lt_top
  obtain ⟨code, hcode, w, hw1, hwm, hwlim, h, hh, hdef, hthermal, hcost⟩ :=
    q oneState one_trace (nativeResolution oneState) (A := Aone)
      (Set.singleton_nonempty _) (isCompact_singleton) Aone_positive Aone_trace henergy
      (continuousOn_singleton _ _) 1 (by norm_num)
  rcases hthermal with ⟨h1, hsum, _, _, _, _, _, _, _, _, _, hfinite, _, _⟩
  let b := (nativeResolution oneState).basis
  have hp (i) : 0 ≤ diagonal b oneState.1 i :=
    (oneState.1.1.nonneg_iff_isPositive.mp oneState.2.1).re_inner_nonneg_right _
  have hmass : (∑' i, ENNReal.ofReal (diagonal b oneState.1 i)) = 1 := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hp (diagonal_hasSum b oneState.1).summable,
      (diagonal_hasSum b oneState.1).tsum_eq, one_trace]
    norm_num
  have hid := (DiagonalEnergy.diagonal_resolvent_energy b h hh hsum oneState.1.1
    (TraceClass.isTraceClass_coe oneState.1)
    (oneState.1.1.nonneg_iff_isPositive.mp oneState.2.1)).2.2.2.1
  have hlow : (1 : ℝ≥0∞) ≤ DiagonalEnergy.stateEnergy b h hh oneState.1.1
      (TraceClass.isTraceClass_coe oneState.1) := by
    rw [hid, ← hmass]
    apply ENNReal.tsum_le_tsum
    intro i
    apply ENNReal.ofReal_le_ofReal
    change diagonal b oneState.1 i ≤ h i * diagonal b oneState.1 i
    nlinarith [hp i, h1 i]
  have hr := ENNReal.toReal_mono (hfinite oneState.1 (by rfl)).ne hlow
  have hz := (hcost oneState.1 (by rfl)).2.2
  change (DiagonalEnergy.stateEnergy b h hh oneState.1.1
    (TraceClass.isTraceClass_coe oneState.1)).toReal ≤ 0 at hz
  norm_num only [ENNReal.toReal_one] at hr
  linarith

def family : Registration arena.{u} (type_of% (@exists_thermalHamiltonian_of_continuous_spectralEnergy.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_thermalHamiltonian_of_continuous_spectralEnergy.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_thermalHamiltonian_of_continuous_spectralEnergy.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.ContinuousEnergyHamiltonian.Conditional.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.ContinuousEnergyHamiltonian.Conditional.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Conditional

namespace Entropy
def arena : Arena where
  signature := signature
  Law R := ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    [TopologicalSpace.SeparableSpace H] {A : Set (TraceClass H)}
    (hne : A.Nonempty) (hclosed : IsClosed A) (hconv : Convex ℝ A)
    (hp : ∀ rho ∈ A, 0 ≤ rho.1)
    (ht : ∀ rho ∈ A, (trace rho.1 (TraceClass.isTraceClass_coe rho)).re = 1)
    (hf : ∀ (rho) (hr : rho ∈ A), spectralEntropy
      (⟨rho, hp rho hr, density_le_one rho (hp rho hr) (ht rho hr)⟩ : Reference H) ≠ ∞)
    (hc : ContinuousOn realEntropy A),
       ∃ gamma ∈ A, IsMaxOn realEntropy A gamma ∧
      ∃ sigma : Reference H, sigma.1 ∈ A ∧
      (∀ rho ∈ A, spectralEnergy sigma rho ≠ ∞ ∧
        spectralEnergy sigma rho ≤ ENNReal.ofReal (realEntropy gamma + Real.log 2) ∧
        (spectralEnergy sigma rho).toReal ≤ realEntropy gamma + Real.log 2) ∧
      ContinuousOn (spectralEnergy sigma) A ∧
      ContinuousOn (fun rho => (spectralEnergy sigma rho).toReal) A ∧
      ∃ (h : (nativeResolution sigma).index → ℝ) (hh : ∀ i, 0 ≤ h i),
        ThermalOn (nativeResolution sigma).basis h hh A ∧
        0 < R.readout () () (2 + realEntropy gamma + Real.log 2) ∧
        ∀ rho ∈ A,
          DiagonalEnergy.stateEnergy (nativeResolution sigma).basis h hh rho.1
            (TraceClass.isTraceClass_coe rho) ≤
              ENNReal.ofReal (2 + realEntropy gamma + Real.log 2) ∧
          (DiagonalEnergy.stateEnergy (nativeResolution sigma).basis h hh rho.1
            (TraceClass.isTraceClass_coe rho)).toReal ≤
              2 + realEntropy gamma + Real.log 2

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro q
  obtain ⟨gamma, hgamma, hmax, sigma, hsigma, henergy, henergycontENN, henergycont,
    h, hh, hthermal, hpos, hbound⟩ :=
    q (A := Aone) (Set.singleton_nonempty _) isClosed_singleton (convex_singleton _)
      Aone_positive Aone_trace Aone_entropy (continuousOn_singleton _ _)
  change (0 : ℝ) < 0 at hpos
  exact (lt_irrefl 0) hpos

def family : Registration arena.{u} (type_of% (@exists_thermalHamiltonian_of_continuous_entropy.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_thermalHamiltonian_of_continuous_entropy.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_thermalHamiltonian_of_continuous_entropy.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.ContinuousEnergyHamiltonian.Entropy.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.ContinuousEnergyHamiltonian.Entropy.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature (fun _ _ z => z) (fun e => nomatch e))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
end Entropy

end Reg.D5.S3.Quantum.Analysis.TraceClass.ContinuousEnergyHamiltonian
