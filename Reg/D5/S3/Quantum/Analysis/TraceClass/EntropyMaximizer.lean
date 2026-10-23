import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.TraceClass.EntropyMaximizer
import Reg.D5.S3.Quantum.Analysis.TraceClass.HellingerEnergy
import Reg.Support.SingleDependentReadout

open scoped ComplexOrder ENNReal
open QuantumLogEnergy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.D5.S3.Quantum.Analysis.TraceClass.HellingerEnergy (oneState one_trace one_entropy K)

noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace Reg.D5.S3.Quantum.Analysis.TraceClass.EntropyMaximizer

abbrev signature : Signature :=
  _root_.Reg.Support.SingleDependentReadout.signature Unit (fun _ => ℝ) (fun _ => ℝ)

def actual : Realization signature :=
  realize signature (fun _ _ z => z) (fun e => nomatch e)

def rejected : Realization signature :=
  realize signature (fun _ _ z => z + 1) (fun e => nomatch e)

def arena : Arena where
  signature := signature
  Law R := ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : Set (TraceClass H)} (hne : A.Nonempty) (hclosed : IsClosed A) (hconv : Convex ℝ A)
    (hp : ∀ rho ∈ A, 0 ≤ rho.1)
    (ht : ∀ rho ∈ A, (trace rho.1 (TraceClass.isTraceClass_coe rho)).re = 1)
    (hf : ∀ (rho) (h : rho ∈ A), spectralEntropy
      (⟨rho, hp rho h, density_le_one rho (hp rho h) (ht rho h)⟩ : Reference H) ≠ ∞)
    (hcont : ContinuousOn realEntropy A),
    BddAbove (realEntropy '' A) ∧
      ∃ gamma ∈ A, IsMaxOn realEntropy A gamma ∧
        (∀ rho ∈ A, R.readout () () ((1 / 8 : ℝ) * ‖rho - gamma‖ ^ 2) ≤
          realEntropy gamma - realEntropy rho) ∧
        ∀ rho ∈ A, IsMaxOn realEntropy A rho → rho = gamma

private theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  let A : Set (TraceClass K) := {oneState.1}
  have hp : ∀ rho ∈ A, 0 ≤ rho.1 := by
    intro rho hr
    obtain rfl := Set.mem_singleton_iff.mp hr
    exact oneState.2.1
  have ht : ∀ rho ∈ A, (trace rho.1 (TraceClass.isTraceClass_coe rho)).re = 1 := by
    intro rho hr
    obtain rfl := Set.mem_singleton_iff.mp hr
    exact one_trace
  have hf : ∀ (rho) (hr : rho ∈ A), spectralEntropy
      (⟨rho, hp rho hr, density_le_one rho (hp rho hr) (ht rho hr)⟩ : Reference K) ≠ ∞ := by
    intro rho hr
    obtain rfl := Set.mem_singleton_iff.mp hr
    change spectralEntropy oneState ≠ ∞
    rw [one_entropy]
    exact ENNReal.zero_ne_top
  obtain ⟨_, gamma, hg, _, hgap, _⟩ := h (A := A) (Set.singleton_nonempty _)
    (isClosed_singleton) (convex_singleton _) hp ht hf (continuousOn_singleton _ _)
  have hh := hgap gamma hg
  norm_num [rejected, realize] at hh

private theorem actual_dependence : ObservationalDependence signature actual := by
  intro i
  refine ⟨(), 0, 1, ?_⟩
  norm_num [actual, realize]

def family : Registration arena.{u} (type_of% (@exists_unique_entropy_maximizer.{u})) where
  actual := actual
  bridge := Iff.rfl
  variation := ⟨@exists_unique_entropy_maximizer.{u}, rejected, rejected_law⟩
  sensitivity := _root_.Reg.Support.SingleDependentReadout.sensitivity
    arena.Law actual rejected rejected_law
  dependence := actual_dependence

def audit : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@exists_unique_entropy_maximizer.{u}) (Realization signature) Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.EntropyMaximizer.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.EntropyMaximizer.family
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

#print axioms audit

end Reg.D5.S3.Quantum.Analysis.TraceClass.EntropyMaximizer
