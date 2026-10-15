import LeanInformationAuditInterface.Contract.Registration
import D5.S3.Quantum.Analysis.TraceClass.CompactCommonReference
import Reg.D5.S3.Quantum.Analysis.TraceClass.HellingerEnergy
import Reg.Support.DependentFamily

open scoped ComplexOrder ENNReal
open QuantumLogEnergy
open _root_.D5.S3.ConceptDynamics.InformationEscape.DependentFamily
open LeanInformationAudit
open Reg.D5.S3.Quantum.Analysis.TraceClass.HellingerEnergy (oneState one_trace one_entropy K)
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace Reg.D5.S3.Quantum.Analysis.TraceClass.CompactCommonReference

private theorem singleton_positive (r : TraceClass K) (hr : r ∈ ({oneState.1} : Set (TraceClass K))) :
    0 ≤ r.1 := by
  obtain rfl := Set.mem_singleton_iff.mp hr
  exact oneState.2.1

private theorem singleton_trace (r : TraceClass K) (hr : r ∈ ({oneState.1} : Set (TraceClass K))) :
    (trace r.1 (TraceClass.isTraceClass_coe r)).re = 1 := by
  obtain rfl := Set.mem_singleton_iff.mp hr
  exact one_trace

private theorem singleton_finite (r : TraceClass K) (hr : r ∈ ({oneState.1} : Set (TraceClass K))) :
    spectralEntropy (⟨r, singleton_positive r hr,
      density_le_one r (singleton_positive r hr) (singleton_trace r hr)⟩ : Reference K) ≠ ∞ := by
  obtain rfl := Set.mem_singleton_iff.mp hr
  change spectralEntropy oneState ≠ ∞
  rw [one_entropy]
  exact ENNReal.zero_ne_top

namespace Center

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ≥0∞
  Role := ULift.{u} Unit
  finiteRole := Fintype.ofSubsingleton ⟨()⟩
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual := realize signature.{u} (fun _ _ z => z) (fun a => nomatch a)
def rejected := realize signature.{u} (fun _ _ _ => ∞) (fun a => nomatch a)

def theoremLaw (R : Realization signature.{u}) : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {C : Set (TraceClass H)}
    (hC : Convex ℝ C)
    (hp : ∀ r ∈ C, 0 ≤ r.1)
    (ht : ∀ r ∈ C, (trace r.1 (TraceClass.isTraceClass_coe r)).re = 1)
    (hf : ∀ (r) (h : r ∈ C), spectralEntropy
      (⟨r, hp r h, density_le_one r (hp r h) (ht r h)⟩ : Reference H) ≠ ∞)
    (g : Reference H) (hg : g.1 ∈ C) (hmax : IsMaxOn realEntropy C g.1)
    (r : TraceClass H) (hr : r ∈ C), R.readout ⟨()⟩ () (spectralEnergy g r) ≤ spectralEntropy g

abbrev arena : Arena where
  signature := signature.{u}
  Law := theoremLaw

theorem actual_law : arena.{u}.Law actual := by
  intro H _ _ _ C hcv hp ht hf g hg hmax r hr
  exact spectralEnergy_le_entropy_of_isMaxOn hcv hp ht hf g hg hmax r hr

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  have hmax : IsMaxOn realEntropy ({oneState.1} : Set (TraceClass K)) oneState.1 := by
    intro r hr
    obtain rfl := Set.mem_singleton_iff.mp hr
    exact le_refl (realEntropy (oneState.1 : TraceClass K))
  have hh := h (C := {oneState.1}) (convex_singleton _) singleton_positive singleton_trace
    singleton_finite oneState (Set.mem_singleton _)
    hmax oneState.1 (Set.mem_singleton _)
  simpa [rejected, realize, one_entropy] using hh

def family : Registration arena.{u} (arena.Law actual) where
  actual := realize signature (fun _ _ z => z) (fun a => nomatch a)
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    simp [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@QuantumLogEnergy.spectralEnergy_le_entropy_of_isMaxOn.{u})
    (type_of% (realize signature.{u} (fun _ _ z => z) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.CompactCommonReference.Center.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.CompactCommonReference.Center.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ z => z) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms registration

end Center

namespace Endpoint

abbrev signature : Signature where
  Params := Unit
  State _ := ℝ≥0∞
  Role := ULift.{u} Unit
  finiteRole := Fintype.ofSubsingleton ⟨()⟩
  nonemptyRole := inferInstance
  Output _ _ := ℝ≥0∞
  Anchor := Empty
  finiteAnchor := inferInstance

def actual := realize signature.{u} (fun _ _ z => z) (fun a => nomatch a)
def rejected := realize signature.{u} (fun _ _ _ => ∞) (fun a => nomatch a)

def theoremLaw (R : Realization signature.{u}) : Prop :=
  ∀ {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    {A : Set (TraceClass H)}
    (hA : IsCompact A) (hne : A.Nonempty) (hcv : Convex ℝ A)
    (hp : ∀ r ∈ A, 0 ≤ r.1)
    (ht : ∀ r ∈ A, (trace r.1 (TraceClass.isTraceClass_coe r)).re = 1)
    (hf : ∀ (r) (h : r ∈ A), spectralEntropy
      (⟨r, hp r h, density_le_one r (hp r h) (ht r h)⟩ : Reference H) ≠ ∞)
    (hc : ContinuousOn realEntropy A),
    ∃ gamma ∈ A, IsMaxOn realEntropy A gamma ∧
      ∃ sigma : Reference H, sigma.1 ∈ A ∧
        (∀ r ∈ A, R.readout ⟨()⟩ () (spectralEnergy sigma r) ≠ ∞ ∧
          R.readout ⟨()⟩ () (spectralEnergy sigma r) ≤ ENNReal.ofReal (realEntropy gamma + Real.log 2) ∧
          (R.readout ⟨()⟩ () (spectralEnergy sigma r)).toReal ≤ realEntropy gamma + Real.log 2) ∧
        ContinuousOn (fun r => R.readout ⟨()⟩ () (spectralEnergy sigma r)) A ∧
        ContinuousOn (fun r => (R.readout ⟨()⟩ () (spectralEnergy sigma r)).toReal) A

abbrev arena : Arena where
  signature := signature.{u}
  Law := theoremLaw

theorem actual_law : arena.{u}.Law actual := by
  intro H _ _ _ A hA hne hcv hp ht hf hc
  exact fullCompactCommonReference hA hne hcv hp ht hf hc

theorem rejected_law : ¬ arena.{u}.Law rejected := by
  intro h
  obtain ⟨gamma, hgamma, hmax, sigma, hsigma, hall, hc, hreal⟩ :=
    h (A := {oneState.1}) isCompact_singleton (Set.singleton_nonempty _)
      (convex_singleton _) singleton_positive singleton_trace singleton_finite
      (continuousOn_singleton _ _)
  have hh := (hall oneState.1 (Set.mem_singleton _)).1
  exact hh rfl

def family : Registration arena.{u} (arena.Law actual) where
  actual := realize signature (fun _ _ z => z) (fun a => nomatch a)
  bridge := Iff.rfl
  variation := ⟨actual_law, rejected, rejected_law⟩
  sensitivity := by
    constructor
    · intro i
      refine ⟨rejected, ?_, rfl, rejected_law⟩
      intro j h
      exact (h (Subsingleton.elim _ _)).elim
    · intro a
      exact nomatch a
  dependence := by
    intro i
    refine ⟨(), 0, 1, ?_⟩
    simp [actual, realize]

def registration : Contract.Registration.{_,_,_,0,0,0,_,_,_,_,_,0}
    (@QuantumLogEnergy.fullCompactCommonReference.{u})
    (type_of% (realize signature.{u} (fun _ _ z => z) (fun a => nomatch a)))
    Unit Unit where
  unitName := `Reg.D5.S3.Quantum.Analysis.TraceClass.CompactCommonReference.Endpoint.unit
  realizationName := `Reg.D5.S3.Quantum.Analysis.TraceClass.CompactCommonReference.Endpoint.family
  realizationSource := none
  generated := false
  arena := .source ⟨arena.{u}⟩
  objectArena := .source ⟨arena.{u}⟩
  catalog := Lean.Name.anonymous
  localNames := false
  realization := .source arena.{u} ⟨family.{u}⟩
  correspondence := { stage := .evidence, objectStage := .evidence }
  bundleNonempty := .absent
  readout := some (realize signature.{u} (fun _ _ z => z) (fun a => nomatch a))
  variation := .absent
  sensitivity := .absent
  partialSensitivity := none
  escapeFrom := none
  sourceSelection := none
  continuation := .unknown
  familyRecord := none
  options := #[]
#print axioms registration

end Endpoint

end Reg.D5.S3.Quantum.Analysis.TraceClass.CompactCommonReference
